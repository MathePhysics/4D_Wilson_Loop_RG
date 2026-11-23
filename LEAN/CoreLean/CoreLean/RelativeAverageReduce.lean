/-
`prop:relative-average` of BALABAN_CORE.tex (`b59f34222bde`): the reduction of a general background to a polydisc.

* `cond_of_ref`, `uniform_polydisc`: the conditions of holomorphy (`Cond`) at `(X, B)` hold on every torus as soon
  as they hold for the box data on the reference torus of size `4h + 2`; hence one radius serves all tori.
* `holG_local`, `expsG_local`: the products along the paths `𝐆(y, x)` depend only on the bonds of `B(y)`.
* `reduce_box`: for a gauge field `U` with `|U(∂p) - id| ≤ α₀` on the plaquettes with corners in `B(c₋) ∪ B(c₊)`
  and `‖aA'‖ ≤ α₁` on the bonds of this box, the axial gauge `u` from `c₋` (`uG`) gives `(e^{iaA'}U)^u = e^{iX}` on
  the bonds of the box, with `‖X‖ ≤ 6α₁ + 2(8h + 2)√Nα₀` (the core's `𝐔^u = 𝐔_X`).
* `relAvg_reduce`, `relLog_reduce`, `Qlin_reduce`, `Crem_reduce`: `𝓜_𝐔(B)(c) = 𝓜_{𝐔_X}(Ad_uB)(c)` and the same
  for the logarithm, the linear part, and the remainder (`u(c₋) = id`).
* `relative_average_vi`: (vi) for the core's `𝐔 = e^{iaA'}U`, with constants which depend on `L` and `G` only.
-/
import CoreLean.RelativeAverageStraight
import CoreLean.AverageDomain
import CoreLean.Transports

open Matrix NormedSpace Filter Topology Metric
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace RelativeAverage

open LatticePaths LatticeKappa RegularAverages BlockPaths AverageHolo MeanTransports AxialReference

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-! ### Transfer of the conditions of holomorphy -/

section Transfer

variable {n n' : ℕ} [NeZero n] [NeZero n']

lemma goodAt_agree {h : ℕ} {V : Config N n} {B : Fin 4 → Site n → Mat} {y : Site n} {V' : Config N n'}
    {B' : Fin 4 → Site n' → Mat} {y' : Site n'} (hA : Agree h V B y V' B' y') {w : Fin 4 → ℤ}
    (hw : EndOK h w) :
    (GoodAt V (ofs y w) h ↔ GoodAt V' (ofs y' w) h) ∧
      (GoodAt (moveC V B) (ofs y w) h ↔ GoodAt (moveC V' B') (ofs y' w) h) := by
  have h1 : ∀ x Γ, holG V (ofs y w) h x Γ = holG V' (ofs y' w) h x Γ := fun x Γ => (holG_agree hA hw x Γ).1
  have h2 : ∀ x Γ, holG (moveC V B) (ofs y w) h x Γ = holG (moveC V' B') (ofs y' w) h x Γ := fun x Γ =>
    (holG_agree hA hw x Γ).2
  have e1 : ∀ x, expsG V (ofs y w) h x = expsG V' (ofs y' w) h x := fun x => by
    funext i; simp only [expsG, h1]
  have e2 : ∀ x, expsG (moveC V B) (ofs y w) h x = expsG (moveC V' B') (ofs y' w) h x := fun x => by
    funext i; simp only [expsG, h2]
  constructor
  · simp only [GoodAt, quotG, e1, h1]
  · simp only [GoodAt, quotG, e2, h2]

lemma loopsGood_agree {h : ℕ} {V : Config N n} {B : Fin 4 → Site n → Mat} {y : Site n} {V' : Config N n'}
    {B' : Fin 4 → Site n' → Mat} {y' : Site n'} (μ : Fin 4) (hA : Agree h V B y V' B' y') :
    (LoopsGood V y μ h ↔ LoopsGood V' y' μ h) ∧
      (LoopsGood (moveC V B) y μ h ↔ LoopsGood (moveC V' B') y' μ h) := by
  have hl : ∀ x Γ Γ', (V.hol (lpath (ι := Pts h) (P := fun x => Ords (offP h x)) y μ (2 * h + 1) (offP h)
      (ordG h) x Γ Γ') = V'.hol (lpath (ι := Pts h) (P := fun x => Ords (offP h x)) y' μ (2 * h + 1) (offP h)
      (ordG h) x Γ Γ')) ∧ ((moveC V B).hol (lpath (ι := Pts h) (P := fun x => Ords (offP h x)) y μ (2 * h + 1)
      (offP h) (ordG h) x Γ Γ') = (moveC V' B').hol (lpath (ι := Pts h) (P := fun x => Ords (offP h x)) y' μ
      (2 * h + 1) (offP h) (ordG h) x Γ Γ')) := fun x Γ Γ' => by
    rw [lpath_map, lpath_map, hol_map, hol_map, hol_map, hol_map]
    exact holI_agree hA _ (ilpath_inR μ h x Γ Γ')
  constructor
  · simp only [LoopsGood, fun x Γ Γ' => (hl x Γ Γ').1]
  · simp only [LoopsGood, fun x Γ Γ' => (hl x Γ Γ').2]

lemma endOK_zero (h : ℕ) : EndOK h 0 := fun σ => by simp; omega

lemma endOK_plus (h : ℕ) (μ : Fin 4) : EndOK h (Pi.single μ ((2 * h + 1 : ℕ) : ℤ)) := fun σ => by
  by_cases hσ : σ = μ
  · subst hσ; simp; omega
  · simp [Pi.single_eq_of_ne hσ]; omega

/-- **The conditions of holomorphy transfer from the reference torus.** -/
theorem cond_of_ref {y : Site n} {μ : Fin 4} {h : ℕ} {X B : Fin 4 → Site n → Mat}
    (hc : Cond (N := N) (0 : Site (4 * h + 2)) μ h (refForm h X y, refForm h B y)) :
    Cond (N := N) y μ h (X, B) := by
  have hA := agree_ref h (UX (N := N) X) B y
  rw [refConfig_UX] at hA
  have e0 : ∀ (m : ℕ) [NeZero m] (z : Site m), ofs z 0 = z := fun m _ z => ofs_zero z
  have g0 := goodAt_agree hA (endOK_zero h)
  have gL := goodAt_agree hA (endOK_plus h μ)
  rw [e0, e0] at g0
  have hl := loopsGood_agree μ hA
  have t0 := fun x => trans_agree hA (endOK_zero h) x
  have tL := fun x => trans_agree hA (endOK_plus h μ) x
  simp only [e0] at t0
  refine ⟨g0.1.2 hc.g0, gL.1.2 hc.g1, g0.2.2 hc.gA0, gL.2.2 hc.gA1, hl.1.2 hc.l0, hl.2.2 hc.lA,
    fun x => ?_, fun x => ?_, ?_⟩
  · simp only [(t0 x).1, (t0 x).2]; exact hc.q0 x
  · have := hc.q1 x
    simp only [cPlus] at this ⊢
    rw [(tL x).1, (tL x).2]; exact this
  · rw [relAvg_transfer μ hA]; exact hc.r

/-- **One polydisc for all tori**: there is `c_i > 0` such that the conditions of holomorphy hold at every pair
`(X, B)` with `‖(X, B)‖ < c_i`, on every torus and at every bond. -/
theorem uniform_polydisc (h : ℕ) (μ : Fin 4) :
    ∃ ci : ℝ, 0 < ci ∧ ∀ {n : ℕ} [NeZero n] (y : Site n) (X B : Fin 4 → Site n → Mat),
      ‖X‖ < ci → ‖B‖ < ci → Cond (N := N) y μ h (X, B) := by
  obtain ⟨ci, hci, hP⟩ := exists_polydisc (N := N) (0 : Site (4 * h + 2)) μ h
  refine ⟨ci, hci, fun {n} _ y X B hX hB => cond_of_ref (hP _ ?_)⟩
  rw [Prod.norm_def]
  exact max_lt ((norm_refForm_le h y X).trans_lt hX) ((norm_refForm_le h y B).trans_lt hB)

end Transfer

/-! ### Locality of the products along the paths -/

variable {n : ℕ} [NeZero n]

theorem holG_local {h : ℕ} (hn : 4 * h + 2 ≤ n) {y : Site n} {V V' : Config N n}
    (hVV : ∀ μ z, Bm y h z → Bm y h (z + unit n μ) → V μ z = V' μ z) (x : Pts h) (Γ : Ords (offP h x)) :
    holG V y h x Γ = holG V' y h x Γ :=
  StraightExtension.hol_congr_of _ fun t ht => by
    have hnd : (ordG h x Γ).Nodup := (ordG_perm h x Γ).nodup_iff.2 (by decide)
    obtain ⟨h1, h2⟩ := stair_in_block hn (offP_inM h x) _ hnd t ht
    exact val_eq_of_pos hVV t h1 h2

theorem expsG_local {h : ℕ} (hn : 4 * h + 2 ≤ n) {y : Site n} {V V' : Config N n}
    (hVV : ∀ μ z, Bm y h z → Bm y h (z + unit n μ) → V μ z = V' μ z) (x : Pts h) :
    expsG V y h x = expsG V' y h x := by
  funext i; simp only [expsG, holG_local hn hVV]

/-! ### The axial gauge on the box -/

lemma hol_unitary' (U : Config N n) (hU : U.IsGaugeField) (γ : List (Bond n)) :
    ((U.hol γ : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ := by
  induction γ with
  | nil => simp [Config.hol]
  | cons b γ ih =>
    rw [hol_cons]
    exact SupportCont.unitary_mul (Transports.val_unitary U hU b) ih

/-- A bond `(z, z + e_ρ)` with both ends in `B(c₋) ∪ B(c₊)`. -/
def BoxBond (y : Site n) (h : ℕ) (μ ρ : Fin 4) (z : Site n) : Prop :=
  (Bm y h z ∨ Bp y h μ z) ∧ (Bm y h (z + unit n ρ) ∨ Bp y h μ (z + unit n ρ))

lemma inBox_of_bmp {h : ℕ} {y : Site n} {μ : Fin 4} {z : Site n} (hz : Bm y h z ∨ Bp y h μ z) :
    LatticePaths.InBox (loD h) (hiD h μ μ) (rep y h z) := by
  rcases hz with hz | hz
  · exact inB_of_inM hz
  · intro σ
    have := hz σ
    simp only [loD, hiD, or_self]
    by_cases hσ : σ = μ
    · have h2 := this.2 hσ; rw [if_pos hσ]; constructor <;> omega
    · have h1 := this.1 hσ; rw [if_neg hσ]; constructor <;> omega

/-- The offsets of the two ends of a bond of the box. -/
lemma box_bond {h : ℕ} (hn : 4 * h + 4 ≤ n) {y : Site n} {μ ρ : Fin 4} {z : Site n}
    (hb : BoxBond y h μ ρ z) :
    LatticePaths.InBox (loD h) (hiD h μ μ) (rep y h z) ∧ LatticePaths.InBox (loD h) (hiD h μ μ) (rep y h z + Pi.single ρ 1) := by
  have hm := inBox_of_bmp hb.1
  have hm' := inBox_of_bmp hb.2
  have e : z + unit n ρ = ofs y (rep y h z + Pi.single ρ 1) := by rw [ofs1, StraightExtension.ofs_rep]
  have hr : rep y h (z + unit n ρ) = rep y h z + Pi.single ρ 1 := by
    rw [e]
    refine rep_ofs y h fun σ => ?_
    have := hm σ
    simp only [loD, hiD, or_self, Pi.add_apply, Pi.single_apply] at this ⊢
    split_ifs at this ⊢ <;> constructor <;> omega
  rw [hr] at hm'
  exact ⟨hm, hm'⟩

/-- **The core's `𝐔^u = 𝐔_X`**: in the axial gauge `u` from `c₋`, the configuration `e^{iaA'}U` is `e^{iX}` on the
bonds of `B(c₋) ∪ B(c₊)`, with `‖X‖ ≤ 4α₁ + 2(8h + 2)β`, where `β` bounds `‖U(∂p) - id‖` on the plaquettes with
corners in the box and `α₁` bounds `‖aA'‖` on its bonds. -/
theorem reduce_box (U : Config N n) (hU : U.IsGaugeField) {h : ℕ} (hn : 4 * h + 4 ≤ n) (y : Site n) (μ : Fin 4)
    {β α₁ : ℝ} (hβ : 0 ≤ β) (hP : PlaqBound U (boxR y (loD h) (hiD h μ μ)) β) (hα0 : 0 ≤ α₁)
    (A' : Fin 4 → Site n → Mat) (hA' : ∀ ρ z, BoxBond y h μ ρ z → ‖A' ρ z‖ ≤ α₁) (hα₁ : α₁ ≤ 1 / 8)
    (hδ : ((8 * h + 2 : ℕ) : ℝ) * β ≤ 1 / 4) :
    ∃ X : Fin 4 → Site n → Mat, ‖X‖ ≤ 4 * α₁ + 2 * (((8 * h + 2 : ℕ) : ℝ) * β) ∧
      ∀ ρ z, BoxBond y h μ ρ z → ((moveC U A').gauge (uG U y h)) ρ z = UX X ρ z := by
  classical
  set u := uG U y h with hu_def
  set δ := ((8 * h + 2 : ℕ) : ℝ) * β with hδ_def
  have hu : ∀ z, ((u z : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ := fun z => hol_unitary' U hU _
  have hUg : (U.gauge u).IsGaugeField := fun ρ z => by
    simp only [Config.gauge, Units.val_mul]
    exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (hu z) (hU ρ z)) (SupportCont.unitary_inv (hu _))
  have hG : ∀ ρ z, BoxBond y h μ ρ z → ‖(((U.gauge u) ρ z : GLN) : Mat) - 1‖ ≤ δ := by
    intro ρ z hb
    obtain ⟨hm, hm'⟩ := box_bond hn hb
    have := gauge_bound U hU hn y μ μ hβ hP (rep y h z) ρ hm hm'
    rwa [StraightExtension.ofs_rep] at this
  set W := (moveC U A').gauge u with hW_def
  have hWe : ∀ ρ z, ((W ρ z : GLN) : Mat) =
      exp (Complex.I • Ad (u z) (A' ρ z)) * (((U.gauge u) ρ z : GLN) : Mat) := fun ρ z => by
    rw [hW_def, ← moveC_gauge]; rfl
  have hsmall : ∀ ρ z, BoxBond y h μ ρ z → ‖((W ρ z : GLN) : Mat) - 1‖ ≤ 2 * α₁ + δ := by
    intro ρ z hb
    have e : ((W ρ z : GLN) : Mat) - 1 = (exp (Complex.I • Ad (u z) (A' ρ z)) - 1) * (((U.gauge u) ρ z : GLN) : Mat) +
        ((((U.gauge u) ρ z : GLN) : Mat) - 1) := by rw [hWe]; noncomm_ring
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add ?_ (hG ρ z hb))
    rw [CStarRing.norm_mul_mem_unitary _ (hUg ρ z)]
    have hA := hA' ρ z hb
    have hn' : ‖Complex.I • Ad (u z) (A' ρ z)‖ ≤ α₁ := by
      rw [norm_I_smul', SupportCont.opNorm_Ad_unitary (hu z)]; exact hA
    exact (BakerCampbellHausdorff.norm_exp_sub_one_le ℂ _).trans
      (exp_sub_one_le_two_mul (norm_nonneg _) hn' (by linarith))
  let X : Fin 4 → Site n → Mat := fun ρ z =>
    if BoxBond y h μ ρ z then (1 / Complex.I) • LogM ((W ρ z : GLN) : Mat) else 0
  have hX : ∀ ρ z, ‖X ρ z‖ ≤ 4 * α₁ + 2 * δ := by
    intro ρ z
    simp only [X]
    split_ifs with hb
    · rw [norm_smul, one_div, norm_inv, Complex.norm_I, _root_.inv_one, one_mul]
      have h1 := hsmall ρ z hb
      refine (norm_LogM_le (by linarith)).trans ?_
      linarith
    · rw [norm_zero]; positivity
  refine ⟨X, (pi_norm_le_iff_of_nonneg (by positivity)).2 fun ρ =>
    (pi_norm_le_iff_of_nonneg (by positivity)).2 fun z => hX ρ z, fun ρ z hb => ?_⟩
  ext1
  have h1 := hsmall ρ z hb
  have hI : Complex.I • X ρ z = LogM ((W ρ z : GLN) : Mat) := by
    simp only [X, if_pos hb, smul_smul]
    rw [mul_one_div_cancel Complex.I_ne_zero, one_smul]
  show ((W ρ z : GLN) : Mat) = ((expU (Complex.I • X ρ z) * (oneC (N := N) ρ z) : GLN) : Mat)
  rw [hI]
  simp only [oneC, mul_one]
  exact (exp_LogM (by linarith)).symm

/-! ### The relative average in the axial gauge -/

lemma uG_base (U : Config N n) {h : ℕ} (hn : 4 * h + 4 ≤ n) (y : Site n) : uG U y h y = 1 := by
  have hr0 : rep y h y = 0 := by
    have := rep_ofs y h (v := 0) (fun σ => by simp only [Pi.zero_apply]; omega)
    rwa [ofs_zero] at this
  rw [uG, hr0]
  simp [stair, segZ_zero, Config.hol]

lemma gauge_gauge_inv (V : Config N n) (u : Site n → GLN) : (V.gauge u).gauge (fun z => (u z)⁻¹) = V := by
  funext ρ z; simp only [Config.gauge]; group

lemma norm_AdF_unitary {u : Site n → GLN} (hu : ∀ z, ((u z : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ)
    (B : Fin 4 → Site n → Mat) : ‖AdF u B‖ = ‖B‖ := by
  have hc : ∀ ρ z, ‖AdF u B ρ z‖ = ‖B ρ z‖ := fun ρ z => SupportCont.opNorm_Ad_unitary (hu z) _
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun ρ => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
      fun z => (hc ρ z).le.trans ((norm_le_pi_norm (B ρ) z).trans (norm_le_pi_norm B ρ))
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun ρ => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
      fun z => (hc ρ z).symm.le.trans ((norm_le_pi_norm (AdF u B ρ) z).trans (norm_le_pi_norm (AdF u B) ρ))

section Gauged

/-- **`𝓜_𝐔(B)(c) = 𝓜_{𝐔_X}(Ad_uB)(c)`** when `𝐔^u = 𝐔_X` on the bonds of the box and the conditions of holomorphy
hold at `(X, Ad_uB)`. -/
theorem relAvg_reduce {U : Config N n} {h : ℕ} {y : Site n} {μ : Fin 4} {A' X : Fin 4 → Site n → Mat} (hU : U.IsGaugeField) (hn : 4 * h + 4 ≤ n)
    (hag : ∀ ρ z, BoxBond y h μ ρ z → ((moveC U A').gauge (uG U y h)) ρ z = UX X ρ z)
    (B : Fin 4 → Site n → Mat) (hc : Cond (N := N) y μ h (X, AdF (uG U y h) B)) :
    relAvg (moveC U A') B y μ h = relAvg (UX X) (AdF (uG U y h) B) y μ h := by
  set u := uG U y h
  set W := (moveC U A').gauge u
  set w : Site n → GLN := fun z => (u z)⁻¹
  have hn2 : 4 * h + 2 ≤ n := by omega
  have hu : ∀ z, ((u z : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ := fun z => hol_unitary' U hU _
  have hw : ∀ z (Z : Mat), ‖Ad (w z) Z‖ ≤ 2 * ‖Z‖ := fun z Z => by
    rw [SupportCont.opNorm_Ad_unitary (SupportCont.unitary_inv (hu z))]; linarith [norm_nonneg Z]
  set B'' := AdF u B
  -- agreement on the blocks
  have hm : ∀ ρ z, Bm y h z → Bm y h (z + unit n ρ) → W ρ z = UX X ρ z := fun ρ z h1 h2 =>
    hag ρ z ⟨Or.inl h1, Or.inl h2⟩
  have hp : ∀ ρ z, Bm (cPlus y μ h) h z → Bm (cPlus y μ h) h (z + unit n ρ) → W ρ z = UX X ρ z :=
    fun ρ z h1 h2 => hag ρ z ⟨Or.inr (bp_of_bm_plus hn2 h1), Or.inr (bp_of_bm_plus hn2 h2)⟩
  have hmv : ∀ (S : Site n → Prop), (∀ ρ z, S z → S (z + unit n ρ) → W ρ z = UX X ρ z) →
      ∀ ρ z, S z → S (z + unit n ρ) → moveC W B'' ρ z = moveC (UX X) B'' ρ z := fun S hS ρ z h1 h2 => by
    simp only [moveC, hS ρ z h1 h2]
  have hY : ∀ x i, ‖expsG W y h x i‖ ≤ 1 / 1024 := fun x i => by
    rw [expsG_local hn2 hm x]; exact hc.g0.expsG_le x i
  have hYA : ∀ x i, ‖expsG (moveC W B'') y h x i‖ ≤ 1 / 1024 := fun x i => by
    rw [expsG_local hn2 (hmv _ hm) x]; exact hc.gA0.expsG_le x i
  have hY' : ∀ x i, ‖expsG W (cPlus y μ h) h x i‖ ≤ 1 / 1024 := fun x i => by
    rw [expsG_local hn2 hp x]; exact hc.g1.expsG_le x i
  have hYA' : ∀ x i, ‖expsG (moveC W B'') (cPlus y μ h) h x i‖ ≤ 1 / 1024 := fun x i => by
    rw [expsG_local hn2 (hmv _ hp) x]; exact hc.gA1.expsG_le x i
  have hg := relAvg_gauge W w B'' y μ h (hw y) (hw _) hY hYA hY' hYA'
  rw [gauge_gauge_inv, AdF_inv'] at hg
  have hw0 : w y = 1 := by simp only [w, u, uG_base U hn y, _root_.inv_one]
  rw [hg, hw0, one_mul, _root_.inv_one, mul_one]
  exact relAvg_local hn2 fun ν z h1 h2 => ⟨hag ν z ⟨h1, h2⟩, rfl⟩

theorem relLog_reduce {U : Config N n} {h : ℕ} {y : Site n} {μ : Fin 4} {A' X : Fin 4 → Site n → Mat} (hU : U.IsGaugeField) (hn : 4 * h + 4 ≤ n)
    (hag : ∀ ρ z, BoxBond y h μ ρ z → ((moveC U A').gauge (uG U y h)) ρ z = UX X ρ z)
    (B : Fin 4 → Site n → Mat) (hc : Cond (N := N) y μ h (X, AdF (uG U y h) B)) :
    relLog (moveC U A') B y μ h = relLog (UX X) (AdF (uG U y h) B) y μ h := by
  simp only [relLog, relAvg_reduce hU hn hag B hc]

/-- **`Q(𝐔) = Q(𝐔_X)Ad_u`**, for `X` in the polydisc of `uniform_polydisc`. -/
theorem Qlin_reduce {U : Config N n} {h : ℕ} {y : Site n} {μ : Fin 4} {A' X : Fin 4 → Site n → Mat} (hU : U.IsGaugeField) (hn : 4 * h + 4 ≤ n)
    (hag : ∀ ρ z, BoxBond y h μ ρ z → ((moveC U A').gauge (uG U y h)) ρ z = UX X ρ z)
    {ci : ℝ} (hci : 0 < ci)
    (hpol : ∀ X' B' : Fin 4 → Site n → Mat, ‖X'‖ < ci → ‖B'‖ < ci → Cond (N := N) y μ h (X', B'))
    (hX : ‖X‖ < ci) :
    Qlin (moveC U A') y μ h = (Qlin (UX X) y μ h).comp (AdFL (uG U y h)) := by
  set u := uG U y h
  have hu : ∀ z, ((u z : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ := fun z => hol_unitary' U hU _
  have heq : (fun B => relLog (moveC U A') B y μ h) =ᶠ[𝓝 0]
      (fun B => relLog (UX X) (AdFL u B) y μ h) := by
    filter_upwards [ball_mem_nhds (0 : Fin 4 → Site n → Mat) hci] with B hB
    rw [mem_ball_zero_iff] at hB
    rw [AdFL_apply]
    exact relLog_reduce hU hn hag B (hpol X _ hX (by rw [norm_AdF_unitary hu]; exact hB))
  have hd : DifferentiableAt ℂ (fun B' => relLog (UX (N := N) X) B' y μ h) (AdFL u 0) := by
    rw [map_zero]
    have h1 := relLog_pair_differentiableAt (hpol X 0 hX (by rw [norm_zero]; exact hci))
    exact h1.comp (f := fun B' : Fin 4 → Site n → Mat => ((X, B') : PairSp N n)) 0
      ((differentiableAt_const X).prodMk differentiableAt_id)
  have hfd : fderiv ℂ (fun B => relLog (moveC U A') B y μ h) 0 =
      (fderiv ℂ (fun B' => relLog (UX (N := N) X) B' y μ h) 0).comp (AdFL u) := by
    rw [heq.fderiv_eq]
    have e : (fun B => relLog (UX (N := N) X) (AdFL u B) y μ h) =
        (fun B' => relLog (UX (N := N) X) B' y μ h) ∘ (AdFL u) := rfl
    rw [e, fderiv_comp 0 hd (AdFL u).differentiableAt, (AdFL u).fderiv, map_zero]
  simp only [Qlin, hfd, ContinuousLinearMap.smul_comp]

theorem Crem_reduce {U : Config N n} {h : ℕ} {y : Site n} {μ : Fin 4} {A' X : Fin 4 → Site n → Mat} (hU : U.IsGaugeField) (hn : 4 * h + 4 ≤ n)
    (hag : ∀ ρ z, BoxBond y h μ ρ z → ((moveC U A').gauge (uG U y h)) ρ z = UX X ρ z)
    {ci : ℝ} (hci : 0 < ci)
    (hpol : ∀ X' B' : Fin 4 → Site n → Mat, ‖X'‖ < ci → ‖B'‖ < ci → Cond (N := N) y μ h (X', B'))
    (hX : ‖X‖ < ci) (B : Fin 4 → Site n → Mat) (hB : ‖B‖ < ci) :
    Crem (moveC U A') B y μ h = Crem (UX X) (AdF (uG U y h) B) y μ h := by
  have hu : ∀ z, ((uG U y h z : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ := fun z => hol_unitary' U hU _
  unfold Crem
  rw [relLog_reduce hU hn hag B (hpol X _ hX (by rw [norm_AdF_unitary hu]; exact hB)),
    Qlin_reduce hU hn hag hci hpol hX, ContinuousLinearMap.comp_apply, AdFL_apply]

end Gauged

/-! ### The derivative of the remainder, uniformly -/

/-- The remainder of `𝐔_X` at the bond `(y, y + Le_μ)` is the remainder of the reference torus, composed with the
box data. -/
lemma Crem_reference {h : ℕ} {μ : Fin 4} {r : ℝ} (hr : 0 < r)
    (hc : ∀ X B : Fin 4 → Site (4 * h + 2) → Mat, ‖X‖ ≤ r → ‖B‖ ≤ r → Cond (N := N) 0 μ h (X, B))
    (y : Site n) (X : Fin 4 → Site n → Mat) (hX : ‖refForm h X y‖ ≤ r) :
    (fun B => Crem (UX (N := N) X) B y μ h) =
      (fun B' => Crem (UX (N := N) (refForm h X y)) B' 0 μ h) ∘ refFormL (N := N) h y := by
  set T := refFormL (N := N) h y
  have hd : DifferentiableAt ℂ (fun B' => relLog (UX (N := N) (refForm h X y)) B' 0 μ h) (T 0) := by
    rw [map_zero]
    exact (relLog_UX_differentiableOn hc hX).differentiableAt (ball_mem_nhds 0 hr)
  have e : (fun B' => relLog (UX (N := N) X) B' y μ h) =
      (fun B' => relLog (UX (N := N) (refForm h X y)) B' 0 μ h) ∘ T := by
    funext B'; simp only [Function.comp_apply]; rw [relLog_reference]; rfl
  have hfd : fderiv ℂ (fun B' => relLog (UX (N := N) X) B' y μ h) 0 =
      (fderiv ℂ (fun B' => relLog (UX (N := N) (refForm h X y)) B' 0 μ h) 0).comp T := by
    rw [e, fderiv_comp 0 hd T.differentiableAt, T.fderiv, map_zero]
  have hL : (((2 * h + 1 : ℕ) : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  funext B
  have hQ : ((2 * h + 1 : ℕ) : ℂ) • Qlin (UX (N := N) X) y μ h B =
      ((2 * h + 1 : ℕ) : ℂ) • Qlin (UX (N := N) (refForm h X y)) 0 μ h (T B) := by
    simp only [Qlin, ContinuousLinearMap.smul_apply, smul_smul, mul_inv_cancel₀ hL, one_smul, hfd,
      ContinuousLinearMap.comp_apply]
  simp only [Function.comp_apply]
  unfold Crem
  rw [hQ, relLog_reference]; rfl

/-- **The derivative of the remainder of `𝐔_X`, uniformly**: `‖DC(𝐔_X; B)δ‖ ≤ C₃‖B‖‖δ‖` for `‖X‖ ≤ r`,
`‖B‖ < r/2`, on every torus. -/
theorem uniform_vi_deriv (h : ℕ) (μ : Fin 4) :
    ∃ r C₃ : ℝ, 0 < r ∧ 0 ≤ C₃ ∧ ∀ {n : ℕ} [NeZero n] (y : Site n) (X B : Fin 4 → Site n → Mat), ‖X‖ ≤ r →
      ‖B‖ < r / 2 → DifferentiableAt ℂ (fun B => Crem (UX (N := N) X) B y μ h) B ∧
        ∀ δ, ‖fderiv ℂ (fun B => Crem (UX (N := N) X) B y μ h) B δ‖ ≤ C₃ * ‖B‖ * ‖δ‖ := by
  obtain ⟨r, K, hr, hK0, hc, hK⟩ := bounds_UX (N := N) (n := 4 * h + 2) 0 μ h
  refine ⟨r, 8 * K / r ^ 2, hr, by positivity, fun {n} _ y X B hX hB => ?_⟩
  set T := refFormL (N := N) h y
  have hX0 : ‖refForm h X y‖ ≤ r := (norm_refForm_le h y X).trans hX
  have hTB : ‖T B‖ < r / 2 := (norm_refForm_le h y B).trans_lt hB
  have e := Crem_reference hr hc y X hX0
  have hdC : DifferentiableAt ℂ (fun B' => Crem (UX (N := N) (refForm h X y)) B' 0 μ h) (T B) :=
    (Crem_UX_differentiableOn hc hX0).differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_zero_iff.2 (by linarith)))
  have hfd : fderiv ℂ (fun B => Crem (UX (N := N) X) B y μ h) B =
      (fderiv ℂ (fun B' => Crem (UX (N := N) (refForm h X y)) B' 0 μ h) (T B)).comp T := by
    rw [e, fderiv_comp B hdC T.differentiableAt, T.fderiv]
  have hdiff : DifferentiableAt ℂ ((fun B' => Crem (UX (N := N) (refForm h X y)) B' 0 μ h) ∘ T) B :=
    hdC.comp B T.differentiableAt
  refine ⟨e ▸ hdiff, fun δ => ?_⟩
  rw [hfd, ContinuousLinearMap.comp_apply]
  have h1 := remainder_deriv_bound_UX hr hc hK hX0 hTB (T δ)
  have h2 : ‖T B‖ ≤ ‖B‖ := norm_refForm_le h y B
  have h3 : ‖T δ‖ ≤ ‖δ‖ := norm_refForm_le h y δ
  have hc0 : 0 ≤ 8 * K / r ^ 2 := by positivity
  refine h1.trans ?_
  have h4 : 8 * K / r ^ 2 * ‖T B‖ ≤ 8 * K / r ^ 2 * ‖B‖ := mul_le_mul_of_nonneg_left h2 hc0
  exact mul_le_mul h4 h3 (norm_nonneg _) (mul_nonneg hc0 (norm_nonneg _))

/-- **The derivative of the remainder for the core's `𝐔`**: where `C(𝐔; ·) = C(𝐔_X; Ad_u ·)` near `B`,
`DC(𝐔; B)δ = DC(𝐔_X; Ad_uB)(Ad_uδ)`. -/
theorem Crem_deriv_reduce {U : Config N n} {h : ℕ} {y : Site n} {μ : Fin 4} {A' X : Fin 4 → Site n → Mat}
    (hU : U.IsGaugeField) (hn : 4 * h + 4 ≤ n)
    (hag : ∀ ρ z, BoxBond y h μ ρ z → ((moveC U A').gauge (uG U y h)) ρ z = UX X ρ z)
    {ci : ℝ} (hci : 0 < ci)
    (hpol : ∀ X' B' : Fin 4 → Site n → Mat, ‖X'‖ < ci → ‖B'‖ < ci → Cond (N := N) y μ h (X', B'))
    (hX : ‖X‖ < ci) {B : Fin 4 → Site n → Mat} (hB : ‖B‖ < ci)
    (hd : DifferentiableAt ℂ (fun B' => Crem (UX (N := N) X) B' y μ h) (AdF (uG U y h) B))
    (δ : Fin 4 → Site n → Mat) :
    fderiv ℂ (fun B' => Crem (moveC U A') B' y μ h) B δ =
      fderiv ℂ (fun B' => Crem (UX (N := N) X) B' y μ h) (AdF (uG U y h) B) (AdF (uG U y h) δ) := by
  set u := uG U y h
  have hu : ∀ z, ((u z : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ := fun z => hol_unitary' U hU _
  have heq : (fun B' => Crem (moveC U A') B' y μ h) =ᶠ[𝓝 B]
      (fun B' => Crem (UX (N := N) X) B' y μ h) ∘ AdFL u := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hB)] with B' hB'
    rw [mem_ball_zero_iff] at hB'
    simp only [Function.comp_apply, AdFL_apply]
    exact Crem_reduce hU hn hag hci hpol hX B' hB'
  rw [heq.fderiv_eq, fderiv_comp B (by rw [AdFL_apply]; exact hd) (AdFL u).differentiableAt, (AdFL u).fderiv,
    ContinuousLinearMap.comp_apply, AdFL_apply, AdFL_apply]

/-! ### The site factors -/

/-- The exponent of the site factor is covariant: `S_{𝐔^u}(Ad_uB)(y) = Ad_{u(y)}S_𝐔(B)(y)`. -/
theorem sExp_gauge (V : Config N n) (u : Site n → GLN) (B : Fin 4 → Site n → Mat) (y : Site n) (h : ℕ)
    (hu : ∀ X : Mat, ‖Ad (u y) X‖ ≤ 2 * ‖X‖) (hY : ∀ x i, ‖expsG V y h x i‖ ≤ 1 / 1024)
    (hYA : ∀ x i, ‖expsG (moveC V B) y h x i‖ ≤ 1 / 1024) :
    sExp (V.gauge u) (AdF u B) y h = Ad (u y) (sExp V B y h) := by
  have e : ∀ x : Pts h, LogM ((trans (moveC (V.gauge u) (AdF u B)) y h x * (trans (V.gauge u) y h x)⁻¹ : GLN) :
      Mat) = Ad (u y) (LogM ((trans (moveC V B) y h x * (trans V y h x)⁻¹ : GLN) : Mat)) := fun x => by
    rw [moveC_gauge, trans_gauge _ _ _ _ _ hu (hYA x), trans_gauge _ _ _ _ _ hu (hY x)]
    rw [show (u y * trans (moveC V B) y h x * (u (ofs y (offP h x)))⁻¹ *
        (u y * trans V y h x * (u (ofs y (offP h x)))⁻¹)⁻¹ : GLN) =
        u y * (trans (moveC V B) y h x * (trans V y h x)⁻¹) * (u y)⁻¹ by group]
    rw [show ((u y * (trans (moveC V B) y h x * (trans V y h x)⁻¹) * (u y)⁻¹ : GLN) : Mat) =
        Ad (u y) ((trans (moveC V B) y h x * (trans V y h x)⁻¹ : GLN) : Mat) by
      simp only [Ad, Units.val_mul], LogM_conj]
  simp only [sExp, e, ← Ad_sum, ← Ad_smul]

/-- The exponent of the site factor depends only on the data on the box, not on the torus. -/
lemma sExp_agree {n' : ℕ} [NeZero n'] {h : ℕ} {V : Config N n} {B : Fin 4 → Site n → Mat} {y : Site n}
    {V' : Config N n'} {B' : Fin 4 → Site n' → Mat} {y' : Site n'} (hA : Agree h V B y V' B' y')
    {w : Fin 4 → ℤ} (hw : EndOK h w) : sExp V B (ofs y w) h = sExp V' B' (ofs y' w) h := by
  simp only [sExp, (trans_agree hA hw _).1, (trans_agree hA hw _).2]

lemma norm_restrictF_le (B : Fin 4 → Site n → Mat) (S : Site n → Prop) [DecidablePred S] :
    ‖restrictF B S‖ ≤ ‖B‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun ν => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun z => by
    simp only [restrictF]
    split_ifs
    · exact (norm_le_pi_norm (B ν) z).trans (norm_le_pi_norm B ν)
    · rw [norm_zero]; exact norm_nonneg _

/-- **The site factors of `𝐔_X`, uniformly**: for the ends `y + w` (`w = 0` or `Le_μ`) of the bond,
`‖S_{𝐔_X}(B)(y + w)‖ ≤ C‖B‖_{∞, B(y + w)}`, on every torus of side `≥ 4h + 2`. -/
theorem uniform_site (h : ℕ) (μ : Fin 4) {w : Fin 4 → ℤ} (hw : EndOK h w) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ∀ {n : ℕ} [NeZero n], 4 * h + 2 ≤ n → ∀ (y : Site n)
      (X B : Fin 4 → Site n → Mat) [DecidablePred (Bm (ofs y w) h)], ‖X‖ ≤ r →
      ‖restrictF B (Bm (ofs y w) h)‖ < r →
      ‖sExp (UX (N := N) X) B (ofs y w) h‖ ≤ C * ‖restrictF B (Bm (ofs y w) h)‖ := by
  classical
  set y₀ : Site (4 * h + 2) := ofs 0 w
  obtain ⟨ci, hci, hcond⟩ := exists_polydisc (N := N) y₀ μ h
  set r := ci / 2 with hr
  have hr0 : 0 < r := by positivity
  have hc : ∀ X B : Fin 4 → Site (4 * h + 2) → Mat, ‖X‖ ≤ r → ‖B‖ ≤ r → Cond (N := N) y₀ μ h (X, B) :=
    fun X B hX hB => hcond _ (norm_pair_lt (by linarith) (by linarith))
  obtain ⟨K', hK'⟩ := exists_site_bound hc
  have hK0 : 0 ≤ K' := (norm_nonneg _).trans (hK' 0 0 (by simp; exact hr0.le) (by simp; exact hr0.le))
  refine ⟨r, K' / r, hr0, by positivity, fun {n} _ hn y X B _ hX hB => ?_⟩
  set B' := restrictF B (Bm (ofs y w) h)
  have hA := agree_ref h (UX (N := N) X) B' y
  rw [refConfig_UX] at hA
  rw [sExp_local hn, sExp_agree hA hw]
  have hX0 : ‖refForm h X y‖ ≤ r := (norm_refForm_le h y X).trans hX
  have hB0 : ‖refForm h B' y‖ ≤ ‖B'‖ := norm_refForm_le h y B'
  have hB1 : ‖restrictF (refForm h B' y) (Bm y₀ h)‖ ≤ ‖B'‖ := (norm_restrictF_le _ _).trans hB0
  calc ‖sExp (UX (N := N) (refForm h X y)) (refForm h B' y) y₀ h‖
      ≤ K' / r * ‖restrictF (refForm h B' y) (Bm y₀ h)‖ :=
        site_bound_UX (le_refl _) hr0 hc hK' hX0 (lt_of_le_of_lt hB1 hB)
    _ ≤ K' / r * ‖B'‖ := mul_le_mul_of_nonneg_left hB1 (by positivity)

lemma restrictF_AdF (u : Site n → GLN) (B : Fin 4 → Site n → Mat) (S : Site n → Prop) [DecidablePred S] :
    restrictF (AdF u B) S = AdF u (restrictF B S) := by
  funext ν z; simp only [restrictF, AdF]; split_ifs <;> simp [Ad]

lemma restrictF_restrictF (B : Fin 4 → Site n → Mat) (S : Site n → Prop) [DecidablePred S] :
    restrictF (restrictF B S) S = restrictF B S := by
  funext ν z; simp only [restrictF]; split_ifs <;> simp_all

/-- **`prop:relative-average`(vi) for the core's `𝐔 = e^{iaA'}U`**: there are `c, C₁, C₂`, depending on `L` (here
`2h + 1`) and `G` only, such that for a gauge field `U` with `|U(∂p) - id| ≤ α₀ ≤ c` (Hilbert–Schmidt norm) on the
plaquettes with corners in `B(c₋) ∪ B(c₊)` and `‖aA'‖ ≤ α₁ ≤ c` on the bonds of this box,
`‖LaQ(𝐔)A‖ ≤ C₁‖aA‖_∞` and, for `‖aA‖_∞ < c`, `‖C(𝐔; aA)(c)‖ ≤ C₂‖aA‖²_∞` and the derivative of the remainder in a
direction `δ` is at most `C₃‖aA‖_∞‖δ‖_∞`, on every torus of side `≥ 4h + 4`. -/
theorem relative_average_vi (h : ℕ) (μ : Fin 4) :
    ∃ c C₁ C₂ C₃ : ℝ, 0 < c ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ 0 ≤ C₃ ∧
      ∀ {n : ℕ} [NeZero n] (U : Config N n), U.IsGaugeField → 4 * h + 4 ≤ n → ∀ (y : Site n) (α₀ α₁ : ℝ),
        0 ≤ α₀ → 0 ≤ α₁ → α₀ ≤ c → α₁ ≤ c →
        (∀ μ' ν' z, PlaqIn (boxR y (loD h) (hiD h μ μ)) μ' ν' z →
          hs (((plaq U μ' ν' z : GLN) : Mat) - 1) ≤ α₀) →
        ∀ A' : Fin 4 → Site n → Mat, (∀ ρ z, BoxBond y h μ ρ z → ‖A' ρ z‖ ≤ α₁) →
        ∀ B : Fin 4 → Site n → Mat,
          ‖((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC U A') y μ h B‖ ≤ C₁ * ‖B‖ ∧
          (‖B‖ < c → ‖Crem (moveC U A') B y μ h‖ ≤ C₂ * ‖B‖ ^ 2) ∧
          (‖B‖ < c → ∀ δ, ‖fderiv ℂ (fun B' => Crem (moveC U A') B' y μ h) B δ‖ ≤ C₃ * ‖B‖ * ‖δ‖) := by
  obtain ⟨ci, hci, hpol⟩ := uniform_polydisc (N := N) h μ
  obtain ⟨r, C₁, C₂, hr, hC₁, hC₂, hvi⟩ := uniform_vi (N := N) h μ
  obtain ⟨r', C₃, hr', hC₃, hder⟩ := uniform_vi_deriv (N := N) h μ
  set K : ℝ := 4 + 2 * (((8 * h + 2 : ℕ) : ℝ) * Real.sqrt N) with hK
  have hK4 : 4 ≤ K := by
    rw [hK]; have : 0 ≤ ((8 * h + 2 : ℕ) : ℝ) * Real.sqrt N := by positivity
    linarith
  have hKpos : 0 < K := by linarith
  set m := min ci (min r (r' / 2)) with hm
  have hm0 : 0 < m := lt_min hci (lt_min hr (by positivity))
  have hmci : m ≤ ci := min_le_left _ _
  have hmr : m ≤ r := (min_le_right _ _).trans (min_le_left _ _)
  have hmr' : m ≤ r' / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨min (m / (2 * K)) (1 / (8 * K)), C₁, C₂, C₃, by positivity, hC₁, hC₂, hC₃, ?_⟩
  intro n _ U hU hn y α₀ α₁ hα₀ hα₁ hα₀c hα₁c hplq A' hA' B
  have hc1 : min (m / (2 * K)) (1 / (8 * K)) ≤ m / (2 * K) := min_le_left _ _
  have hc2 : min (m / (2 * K)) (1 / (8 * K)) ≤ 1 / (8 * K) := min_le_right _ _
  set β := Real.sqrt N * α₀ with hβ
  have hβ0 : 0 ≤ β := by positivity
  have hP : PlaqBound U (boxR y (loD h) (hiD h μ μ)) β := fun μ' ν' z _ hz =>
    (opNorm_le_sqrt_mul_hs _).trans (mul_le_mul_of_nonneg_left (hplq μ' ν' z hz) (Real.sqrt_nonneg _))
  -- the smallness conditions
  have h8K : 1 / (8 * K) ≤ 1 / 8 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hα18 : α₁ ≤ 1 / 8 := (hα₁c.trans hc2).trans h8K
  have e2 : ((8 * h + 2 : ℕ) : ℝ) * β ≤ K / 2 * α₀ := by
    rw [hβ, hK]
    have : 0 ≤ α₀ := hα₀
    nlinarith [Real.sqrt_nonneg (N : ℝ), (Nat.cast_nonneg _ : (0 : ℝ) ≤ ((8 * h + 2 : ℕ) : ℝ))]
  have e3 : K / 2 * α₀ ≤ K / 2 * (1 / (8 * K)) := mul_le_mul_of_nonneg_left (hα₀c.trans hc2) (by linarith)
  have e4 : K / 2 * (1 / (8 * K)) = 1 / 16 := by field_simp; ring
  have hδ14 : ((8 * h + 2 : ℕ) : ℝ) * β ≤ 1 / 4 := by linarith
  obtain ⟨X, hXn, hag⟩ := reduce_box U hU hn y μ hβ0 hP hα₁ A' hA' hα18 hδ14
  -- `‖X‖ ≤ K c ≤ m/2`
  have hXK : ‖X‖ ≤ m / 2 := by
    have e2 : ((8 * h + 2 : ℕ) : ℝ) * β ≤ ((8 * h + 2 : ℕ) : ℝ) * Real.sqrt N *
        min (m / (2 * K)) (1 / (8 * K)) := by
      rw [hβ, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left hα₀c (by positivity)
    have e3 : 4 * α₁ ≤ 4 * min (m / (2 * K)) (1 / (8 * K)) := by linarith
    have e4 : K * min (m / (2 * K)) (1 / (8 * K)) ≤ K * (m / (2 * K)) := mul_le_mul_of_nonneg_left hc1 hKpos.le
    have e5 : K * (m / (2 * K)) = m / 2 := by field_simp
    calc ‖X‖ ≤ 4 * α₁ + 2 * (((8 * h + 2 : ℕ) : ℝ) * β) := hXn
      _ ≤ K * min (m / (2 * K)) (1 / (8 * K)) := by rw [hK]; nlinarith
      _ ≤ m / 2 := by linarith
  have hXci : ‖X‖ < ci := lt_of_le_of_lt hXK (by linarith)
  have hXr : ‖X‖ ≤ r := hXK.trans (by linarith)
  have hXr' : ‖X‖ ≤ r' := hXK.trans (by linarith)
  have hpol' : ∀ X' B' : Fin 4 → Site n → Mat, ‖X'‖ < ci → ‖B'‖ < ci → Cond (N := N) y μ h (X', B') :=
    fun X' B' => hpol y X' B'
  have hu : ∀ z, ((uG U y h z : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ := fun z => hol_unitary' U hU _
  obtain ⟨hlin, hrem⟩ := hvi y X (AdF (uG U y h) B) hXr
  have hcm : min (m / (2 * K)) (1 / (8 * K)) ≤ m := hc1.trans (by
    rw [div_le_iff₀ (by positivity)]; nlinarith)
  refine ⟨?_, fun hB => ?_, fun hB δ => ?_⟩
  · rw [Qlin_reduce hU hn hag hci hpol' hXci, ContinuousLinearMap.comp_apply, AdFL_apply]
    rw [norm_AdF_unitary hu] at hlin
    exact hlin
  · have hBci : ‖B‖ < ci := lt_of_lt_of_le hB (hcm.trans hmci)
    have hBr : ‖AdF (uG U y h) B‖ < r := by
      rw [norm_AdF_unitary hu]; exact lt_of_lt_of_le hB (hcm.trans hmr)
    rw [Crem_reduce hU hn hag hci hpol' hXci B hBci]
    have := hrem hBr
    rwa [norm_AdF_unitary hu] at this
  · have hBci : ‖B‖ < ci := lt_of_lt_of_le hB (hcm.trans hmci)
    have hBr' : ‖AdF (uG U y h) B‖ < r' / 2 := by
      rw [norm_AdF_unitary hu]; exact lt_of_lt_of_le hB (hcm.trans hmr')
    obtain ⟨hd, hbd⟩ := hder y X (AdF (uG U y h) B) hXr' hBr'
    rw [Crem_deriv_reduce hU hn hag hci hpol' hXci hBci hd δ]
    have := hbd (AdF (uG U y h) δ)
    rwa [norm_AdF_unitary hu, norm_AdF_unitary hu] at this


/-- The constant `K = 4 + 2(8h + 2)√N` of the reduction. -/
def redK (N h : ℕ) : ℝ := 4 + 2 * (((8 * h + 2 : ℕ) : ℝ) * Real.sqrt N)

lemma four_le_redK (N h : ℕ) : 4 ≤ redK N h := by
  unfold redK; have : 0 ≤ ((8 * h + 2 : ℕ) : ℝ) * Real.sqrt N := by positivity
  linarith

/-- **The reduction with explicit smallness**: for `α₀, α₁ ≤ c₀ ≤ 1/(8K)`, the axial gauge gives `𝐔^u = 𝐔_X` on the
bonds of the box with `‖X‖ ≤ Kc₀`. -/
theorem reduce_small {h : ℕ} {U : Config N n} (hU : U.IsGaugeField) (hn : 4 * h + 4 ≤ n) (y : Site n)
    (μ : Fin 4) {α₀ α₁ c₀ : ℝ} (hα₀ : 0 ≤ α₀) (hα₁ : 0 ≤ α₁) (hα₀c : α₀ ≤ c₀) (hα₁c : α₁ ≤ c₀)
    (hc₀ : c₀ ≤ 1 / (8 * redK N h))
    (hplq : ∀ μ' ν' z, PlaqIn (boxR y (loD h) (hiD h μ μ)) μ' ν' z →
      hs (((plaq U μ' ν' z : GLN) : Mat) - 1) ≤ α₀)
    (A' : Fin 4 → Site n → Mat) (hA' : ∀ ρ z, BoxBond y h μ ρ z → ‖A' ρ z‖ ≤ α₁) :
    ∃ X : Fin 4 → Site n → Mat, ‖X‖ ≤ redK N h * c₀ ∧ ‖X‖ ≤ redK N h * (α₀ + α₁) ∧
      ∀ ρ z, BoxBond y h μ ρ z → ((moveC U A').gauge (uG U y h)) ρ z = UX X ρ z := by
  set K := redK N h with hK
  have hK4 : 4 ≤ K := four_le_redK N h
  have hKpos : 0 < K := by linarith
  set β := Real.sqrt N * α₀ with hβ
  have hβ0 : 0 ≤ β := by positivity
  have hP : PlaqBound U (boxR y (loD h) (hiD h μ μ)) β := fun μ' ν' z _ hz =>
    (opNorm_le_sqrt_mul_hs _).trans (mul_le_mul_of_nonneg_left (hplq μ' ν' z hz) (Real.sqrt_nonneg _))
  have h8K : 1 / (8 * K) ≤ 1 / 8 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hα18 : α₁ ≤ 1 / 8 := (hα₁c.trans hc₀).trans h8K
  have e2 : ((8 * h + 2 : ℕ) : ℝ) * β ≤ K / 2 * α₀ := by
    rw [hβ, hK, redK]
    nlinarith [Real.sqrt_nonneg (N : ℝ), (Nat.cast_nonneg _ : (0 : ℝ) ≤ ((8 * h + 2 : ℕ) : ℝ))]
  have e3 : K / 2 * α₀ ≤ K / 2 * (1 / (8 * K)) := mul_le_mul_of_nonneg_left (hα₀c.trans hc₀) (by linarith)
  have e4 : K / 2 * (1 / (8 * K)) = 1 / 16 := by field_simp; ring
  have hδ14 : ((8 * h + 2 : ℕ) : ℝ) * β ≤ 1 / 4 := by linarith
  obtain ⟨X, hXn, hag⟩ := reduce_box U hU hn y μ hβ0 hP hα₁ A' hA' hα18 hδ14
  have hXa : ‖X‖ ≤ K * (α₀ + α₁) := by
    have e6 : 2 * (((8 * h + 2 : ℕ) : ℝ) * β) ≤ K * α₀ := by
      rw [hβ, hK, redK]
      nlinarith [Real.sqrt_nonneg (N : ℝ), (Nat.cast_nonneg _ : (0 : ℝ) ≤ ((8 * h + 2 : ℕ) : ℝ))]
    have e7 : 4 * α₁ ≤ K * α₁ := mul_le_mul_of_nonneg_right hK4 hα₁
    linarith
  refine ⟨X, ?_, hXa, hag⟩
  have e5 : ((8 * h + 2 : ℕ) : ℝ) * β ≤ ((8 * h + 2 : ℕ) : ℝ) * Real.sqrt N * c₀ := by
    rw [hβ, ← mul_assoc]; exact mul_le_mul_of_nonneg_left hα₀c (by positivity)
  calc ‖X‖ ≤ 4 * α₁ + 2 * (((8 * h + 2 : ℕ) : ℝ) * β) := hXn
    _ ≤ K * c₀ := by rw [hK, redK]; nlinarith

/-- **The site factors of the core's `𝐔`**: at the ends `y + w` of the bond (`w = 0` or `Le_μ`),
`‖S_𝐔(B)(y + w)‖ ≤ C‖B‖_{∞, B(y + w)}` for `‖B‖_{∞, B(y + w)} < c`, with `c, C` depending on `L` and `G` only. -/
theorem relative_average_site (h : ℕ) (μ : Fin 4) {w : Fin 4 → ℤ}
    (hw : w = 0 ∨ w = Pi.single μ ((2 * h + 1 : ℕ) : ℤ)) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
      ∀ {n : ℕ} [NeZero n] (U : Config N n), U.IsGaugeField → 4 * h + 4 ≤ n → ∀ (y : Site n) (α₀ α₁ : ℝ),
        0 ≤ α₀ → 0 ≤ α₁ → α₀ ≤ c → α₁ ≤ c →
        (∀ μ' ν' z, PlaqIn (boxR y (loD h) (hiD h μ μ)) μ' ν' z →
          hs (((plaq U μ' ν' z : GLN) : Mat) - 1) ≤ α₀) →
        ∀ A' : Fin 4 → Site n → Mat, (∀ ρ z, BoxBond y h μ ρ z → ‖A' ρ z‖ ≤ α₁) →
        ∀ (B : Fin 4 → Site n → Mat) [DecidablePred (Bm (ofs y w) h)],
          ‖restrictF B (Bm (ofs y w) h)‖ < c →
          ‖sExp (moveC U A') B (ofs y w) h‖ ≤ C * ‖restrictF B (Bm (ofs y w) h)‖ := by
  have hwOK : EndOK h w := by rcases hw with rfl | rfl; exacts [endOK_zero h, endOK_plus h μ]
  obtain ⟨ci, hci, hpol⟩ := uniform_polydisc (N := N) h μ
  obtain ⟨r, C, hr, hC, hsite⟩ := uniform_site (N := N) h μ hwOK
  set K := redK N h
  have hKpos : 0 < K := by linarith [four_le_redK N h]
  set m := min ci r with hm
  have hm0 : 0 < m := lt_min hci hr
  set c := min (m / (2 * K)) (1 / (8 * K)) with hc_def
  have hc1 : c ≤ m / (2 * K) := min_le_left _ _
  have hc2 : c ≤ 1 / (8 * K) := min_le_right _ _
  have hcm : c ≤ m := hc1.trans (by rw [div_le_iff₀ (by positivity)]; nlinarith [four_le_redK N h])
  refine ⟨c, C, by positivity, hC, ?_⟩
  intro n _ U hU hn y α₀ α₁ hα₀ hα₁ hα₀c hα₁c hplq A' hA' B _ hB
  obtain ⟨X, hXn, -, hag⟩ := reduce_small hU hn y μ hα₀ hα₁ hα₀c hα₁c hc2 hplq A' hA'
  have hXm : ‖X‖ ≤ m / 2 := hXn.trans (by
    calc K * c ≤ K * (m / (2 * K)) := mul_le_mul_of_nonneg_left hc1 hKpos.le
      _ = m / 2 := by field_simp)
  have hXci : ‖X‖ < ci := lt_of_le_of_lt hXm (by have := min_le_left ci r; linarith)
  have hXr : ‖X‖ ≤ r := hXm.trans (by have := min_le_right ci r; linarith)
  have hn2 : 4 * h + 2 ≤ n := by omega
  set u := uG U y h
  set W := (moveC U A').gauge u
  set wg : Site n → GLN := fun z => (u z)⁻¹
  obtain ⟨B', hB'def⟩ : ∃ B', B' = restrictF B (Bm (ofs y w) h) := ⟨_, rfl⟩
  rw [← hB'def] at hB ⊢
  have hu : ∀ z, ((u z : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ := fun z => hol_unitary' U hU _
  have hB'ci : ‖AdF u B'‖ < ci := by
    rw [norm_AdF_unitary hu]; exact lt_of_lt_of_le hB (hcm.trans (min_le_left _ _))
  have hcd := hpol y X (AdF u B') hXci hB'ci
  -- agreement on the block of `(ofs y w)`
  have hagr : ∀ ρ z, Bm (ofs y w) h z → Bm (ofs y w) h (z + unit n ρ) → W ρ z = UX X ρ z := by
    intro ρ z h1 h2
    rcases hw with rfl | rfl
    · rw [ofs_zero] at h1 h2
      exact hag ρ z ⟨Or.inl h1, Or.inl h2⟩
    · exact hag ρ z ⟨Or.inr (bp_of_bm_plus hn2 h1), Or.inr (bp_of_bm_plus hn2 h2)⟩
  have hmv : ∀ ρ z, Bm (ofs y w) h z → Bm (ofs y w) h (z + unit n ρ) →
      moveC W (AdF u B') ρ z = moveC (UX X) (AdF u B') ρ z := fun ρ z h1 h2 => by
    simp only [moveC, hagr ρ z h1 h2]
  have hgood : GoodAt (UX (N := N) X) (ofs y w) h ∧ GoodAt (moveC (UX (N := N) X) (AdF u B')) (ofs y w) h := by
    rcases hw with rfl | rfl
    · rw [ofs_zero]; exact ⟨hcd.g0, hcd.gA0⟩
    · exact ⟨hcd.g1, hcd.gA1⟩
  have hY : ∀ x i, ‖expsG W (ofs y w) h x i‖ ≤ 1 / 1024 := fun x i => by
    rw [expsG_local hn2 hagr x]; exact hgood.1.expsG_le x i
  have hYA : ∀ x i, ‖expsG (moveC W (AdF u B')) (ofs y w) h x i‖ ≤ 1 / 1024 := fun x i => by
    rw [expsG_local hn2 hmv x]; exact hgood.2.expsG_le x i
  have hwg : ∀ Z : Mat, ‖Ad (wg (ofs y w)) Z‖ ≤ 2 * ‖Z‖ := fun Z => by
    rw [SupportCont.opNorm_Ad_unitary (SupportCont.unitary_inv (hu _))]; linarith [norm_nonneg Z]
  have hg := sExp_gauge W wg (AdF u B') (ofs y w) h hwg hY hYA
  rw [gauge_gauge_inv, AdF_inv'] at hg
  have hloc : sExp W (AdF u B') (ofs y w) h = sExp (UX (N := N) X) (AdF u B') (ofs y w) h := by
    simp only [sExp, trans_local hn2 hagr, trans_local hn2 hmv]
  rw [sExp_local hn2, ← hB'def, hg, SupportCont.opNorm_Ad_unitary (SupportCont.unitary_inv (hu _)), hloc]
  have hrr : restrictF (AdF u B') (Bm (ofs y w) h) = AdF u B' := by
    rw [restrictF_AdF, hB'def, restrictF_restrictF]
  have hBr : ‖restrictF (AdF u B') (Bm (ofs y w) h)‖ < r := by
    rw [hrr, norm_AdF_unitary hu]; exact lt_of_lt_of_le hB (hcm.trans (min_le_right _ _))
  have := hsite hn2 y X (AdF u B') hXr hBr
  rwa [hrr, norm_AdF_unitary hu] at this


/-! ### The straight average `Q₀` -/

lemma mem_seg_mono (ρ : Fin 4) (s : Bool) : ∀ (j k : ℕ) (z : Site n), j ≤ k → ∀ t ∈ seg ρ s z j, t ∈ seg ρ s z k
  | 0, _, _, _, t, ht => by simp [seg] at ht
  | j + 1, k + 1, z, hjk, t, ht => by
    simp only [seg, List.mem_cons] at ht ⊢
    rcases ht with rfl | ht
    · exact Or.inl rfl
    · exact Or.inr (mem_seg_mono ρ s j k _ (by omega) t ht)
  | _ + 1, 0, _, hjk, _, _ => by omega

/-- The paths `Γ_b` run through bonds with both ends in `B(c₋) ∪ B(c₊)`. -/
lemma pathGb_in {h : ℕ} (hn : 4 * h + 2 ≤ n) (y : Site n) (μ : Fin 4) (x : Pts h) (Γ : Ords (offP h x))
    {j : ℕ} (hj : j ≤ 2 * h + 1) : ∀ t ∈ pathGb y μ h x Γ j,
      (Bm y h t.site ∨ Bp y h μ t.site) ∧ (Bm y h t.plus ∨ Bp y h μ t.plus) := by
  intro t ht
  have hnd : (ordG h x Γ).Nodup := (ordG_perm h x Γ).nodup_iff.2 (by decide)
  simp only [pathGb, List.mem_append] at ht
  rcases ht with ht | ht
  · exact (StraightExtension.paths_in hn μ (offP_inM h x) _ hnd).1 t ht
  · refine (StraightExtension.paths_in hn μ (offP_inM h x) [] List.nodup_nil).2.2 t ?_
    have e : segZ μ (ofs y (offP h x)) ((2 * h + 1 : ℕ) : ℤ) = seg μ true (ofs y (offP h x)) (2 * h + 1) := by
      rw [segZ, if_pos (by positivity)]
      congr 1
    rw [e]
    exact mem_seg_mono μ true j (2 * h + 1) _ hj t ht

/-- **Locality of `Q₀`**: `Q₀(𝐔)` depends only on the values of `𝐔` on the bonds of `B(c₋) ∪ B(c₊)`. -/
theorem Q0L_local {h : ℕ} (hn : 4 * h + 2 ≤ n) {y : Site n} {μ : Fin 4} {V V' : Config N n}
    (hVV : ∀ ν z, (Bm y h z ∨ Bp y h μ z) → (Bm y h (z + unit n ν) ∨ Bp y h μ (z + unit n ν)) →
      V ν z = V' ν z) :
    Q0L V y μ h = Q0L V' y μ h := by
  have hval := val_eq_of_pos (S := fun z => Bm y h z ∨ Bp y h μ z) hVV
  have hp : ∀ x Γ, ∀ j ∈ Finset.range (2 * h + 1), V.hol (pathGb y μ h x Γ j) = V'.hol (pathGb y μ h x Γ j) :=
    fun x Γ j hj => StraightExtension.hol_congr_of _ fun t ht =>
      hval t (pathGb_in hn y μ x Γ (Finset.mem_range.1 hj).le t ht).1
        (pathGb_in hn y μ x Γ (Finset.mem_range.1 hj).le t ht).2
  have hx : ∀ x : Pts h, (∑ Γ : Ords (offP h x), ∑ j ∈ Finset.range (2 * h + 1),
      (AdL (V.hol (pathGb y μ h x Γ j))).comp (evalL μ (ofs y (offP h x) + j • unit n μ))) =
      ∑ Γ : Ords (offP h x), ∑ j ∈ Finset.range (2 * h + 1),
      (AdL (V'.hol (pathGb y μ h x Γ j))).comp (evalL μ (ofs y (offP h x) + j • unit n μ)) := fun x =>
    Finset.sum_congr rfl fun Γ _ => Finset.sum_congr rfl fun j hj => by rw [hp x Γ j hj]
  simp only [Q0L, hx]

lemma Ad_mul' (W W' : GLN) (Z : Mat) : Ad (W * W') Z = Ad W (Ad W' Z) := by
  simp only [Ad, Units.val_mul, _root_.mul_inv_rev]; noncomm_ring

/-- **Covariance of `Q₀`**: `Q₀(𝐔^u)Ad_uB = Ad_{u(c₋)}Q₀(𝐔)B`. -/
theorem Q0L_gauge (V : Config N n) (u : Site n → GLN) (y : Site n) (μ : Fin 4) (h : ℕ)
    (B : Fin 4 → Site n → Mat) : Q0L (V.gauge u) y μ h (AdF u B) = Ad (u y) (Q0L V y μ h B) := by
  have hpath : ∀ x Γ j, (V.gauge u).hol (pathGb y μ h x Γ j) =
      u y * V.hol (pathGb y μ h x Γ j) * (u (ofs y (offP h x) + j • unit n μ))⁻¹ := fun x Γ j => by
    have hc := chain_endpt_stair y (offP h x) (ordG h x Γ) 0
    rw [ofs_zero, zero_add, offs_perm _ (ordG_perm h x Γ)] at hc
    have hch : Chain y (pathGb y μ h x Γ j) := chain_append _ _ _ hc.1 (by rw [hc.2]; exact chain_seg _ _ _ _)
    have he : endpt y (pathGb y μ h x Γ j) = ofs y (offP h x) + j • unit n μ := by
      rw [pathGb, endpt_append, hc.2, endpt_seg]; simp [dvec]
    rw [hol_gauge V u _ y hch, he]
  simp only [Q0L, ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.comp_apply, AdL_apply, evalL_apply, hpath, AdF]
  have e : ∀ x Γ j, Ad (u y * V.hol (pathGb y μ h x Γ j) * (u (ofs y (offP h x) + j • unit n μ))⁻¹)
      (Ad (u (ofs y (offP h x) + j • unit n μ)) (B μ (ofs y (offP h x) + j • unit n μ))) =
      Ad (u y) (Ad (V.hol (pathGb y μ h x Γ j)) (B μ (ofs y (offP h x) + j • unit n μ))) := fun x Γ j => by
    rw [← Ad_mul', ← Ad_mul']; congr 1; group
  simp only [e, ← Ad_sum, ← Ad_smul]

/-- The integer path of `Γ_b`. -/
def ipathGb (μ : Fin 4) (h : ℕ) (x : Pts h) (Γ : Ords (offP h x)) (j : ℕ) : List IBond :=
  istair (offP h x) (ordG h x Γ) 0 ++ iseg μ true (offP h x) j

lemma pathGb_map (y : Site n) (μ : Fin 4) (h : ℕ) (x : Pts h) (Γ : Ords (offP h x)) (j : ℕ) :
    pathGb y μ h x Γ j = (ipathGb μ h x Γ j).map (ib y) := by
  simp only [pathGb, ipathGb, List.map_append]
  rw [stair_map, seg_map]

lemma ipathGb_inR (μ : Fin 4) (h : ℕ) (x : Pts h) (Γ : Ords (offP h x)) {j : ℕ} (hj : j ≤ 2 * h + 1) :
    ∀ b ∈ ipathGb μ h x Γ j, InR h (ipos b) := by
  have hc := offP_inM h x
  intro b hb
  simp only [ipathGb, List.mem_append] at hb
  rcases hb with hb | hb
  · exact block_inR (endOK_zero h) x Γ b hb
  · intro σ
    obtain ⟨h1, -, h3⟩ := ipos_iseg μ true j (offP h x) b hb
    simp only [↓reduceIte] at h3
    have := hc σ
    by_cases hσ : σ = μ
    · subst hσ; constructor <;> omega
    · rw [h1 σ hσ]; constructor <;> omega

lemma ofs_add_nsmul (y : Site n) (c : Fin 4 → ℤ) (μ : Fin 4) (j : ℕ) :
    ofs y c + j • unit n μ = ofs y (c + Pi.single μ (j : ℤ)) := by
  rw [ofs_add_single, natCast_zsmul]

/-- **`Q₀` depends only on the data on the box, not on the torus.** -/
theorem Q0L_agree {n' : ℕ} [NeZero n'] {h : ℕ} {V : Config N n} {B : Fin 4 → Site n → Mat} {y : Site n}
    {V' : Config N n'} {B' : Fin 4 → Site n' → Mat} {y' : Site n'} (μ : Fin 4) (hA : Agree h V B y V' B' y') :
    Q0L V y μ h B = Q0L V' y' μ h B' := by
  have hp : ∀ x Γ, ∀ j ∈ Finset.range (2 * h + 1), V.hol (pathGb y μ h x Γ j) = V'.hol (pathGb y' μ h x Γ j) :=
    fun x Γ j hj => by
      rw [pathGb_map, pathGb_map, hol_map, hol_map]
      exact (holI_agree hA _ (ipathGb_inR μ h x Γ (Finset.mem_range.1 hj).le)).1
  have hb : ∀ x, ∀ j ∈ Finset.range (2 * h + 1), B μ (ofs y (offP h x) + j • unit n μ) =
      B' μ (ofs y' (offP h x) + j • unit n' μ) := fun x j hj => by
    rw [ofs_add_nsmul, ofs_add_nsmul]
    refine (hA _ (fun σ => ?_) μ).2
    have := offP_inM h x σ
    have hj' := Finset.mem_range.1 hj
    simp only [Pi.add_apply, Pi.single_apply]
    split_ifs <;> constructor <;> omega
  have hx : ∀ x : Pts h, (∑ Γ : Ords (offP h x), ∑ j ∈ Finset.range (2 * h + 1),
      Ad (V.hol (pathGb y μ h x Γ j)) (B μ (ofs y (offP h x) + j • unit n μ))) =
      ∑ Γ : Ords (offP h x), ∑ j ∈ Finset.range (2 * h + 1),
      Ad (V'.hol (pathGb y' μ h x Γ j)) (B' μ (ofs y' (offP h x) + j • unit n' μ)) := fun x =>
    Finset.sum_congr rfl fun Γ _ => Finset.sum_congr rfl fun j hj => by rw [hp x Γ j hj, hb x j hj]
  simp only [Q0L, ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.comp_apply, AdL_apply, evalL_apply, hx]

/-- `LQ(𝐔_X)` at the bond `(y, y + Le_μ)` is `LQ` of the reference torus at the box data. -/
lemma Qlin_reference {h : ℕ} {μ : Fin 4} {r : ℝ} (hr : 0 < r)
    (hc : ∀ X B : Fin 4 → Site (4 * h + 2) → Mat, ‖X‖ ≤ r → ‖B‖ ≤ r → Cond (N := N) 0 μ h (X, B))
    (y : Site n) (X : Fin 4 → Site n → Mat) (hX : ‖refForm h X y‖ ≤ r) (B : Fin 4 → Site n → Mat) :
    ((2 * h + 1 : ℕ) : ℂ) • Qlin (UX (N := N) X) y μ h B =
      ((2 * h + 1 : ℕ) : ℂ) • Qlin (UX (N := N) (refForm h X y)) 0 μ h (refForm h B y) := by
  set T := refFormL (N := N) h y
  have hd : DifferentiableAt ℂ (fun B' => relLog (UX (N := N) (refForm h X y)) B' 0 μ h) (T 0) := by
    rw [map_zero]
    exact (relLog_UX_differentiableOn hc hX).differentiableAt (ball_mem_nhds 0 hr)
  have e : (fun B' => relLog (UX (N := N) X) B' y μ h) =
      (fun B' => relLog (UX (N := N) (refForm h X y)) B' 0 μ h) ∘ T := by
    funext B'; simp only [Function.comp_apply]; rw [relLog_reference]; rfl
  have hfd : fderiv ℂ (fun B' => relLog (UX (N := N) X) B' y μ h) 0 =
      (fderiv ℂ (fun B' => relLog (UX (N := N) (refForm h X y)) B' 0 μ h) 0).comp T := by
    rw [e, fderiv_comp 0 hd T.differentiableAt, T.fderiv, map_zero]
  have hL : (((2 * h + 1 : ℕ) : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  simp only [Qlin, ContinuousLinearMap.smul_apply, smul_smul, mul_inv_cancel₀ hL, one_smul, hfd,
    ContinuousLinearMap.comp_apply]
  rfl

/-- **(v) for `𝐔_X`, uniformly**: `‖LQ(𝐔_X)B - LQ₀(𝐔_X)B‖ ≤ C‖X‖‖B‖` for `‖X‖ ≤ r`, on every torus. -/
theorem uniform_v (h : ℕ) (μ : Fin 4) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ∀ {n : ℕ} [NeZero n] (y : Site n) (X B : Fin 4 → Site n → Mat), ‖X‖ ≤ r →
      ‖((2 * h + 1 : ℕ) : ℂ) • Qlin (UX (N := N) X) y μ h B - Q0L (UX (N := N) X) y μ h B‖ ≤ C * ‖X‖ * ‖B‖ := by
  obtain ⟨r, K, hr, hK0, hc, hK⟩ := bounds_UX (N := N) (n := 4 * h + 2) 0 μ h
  obtain ⟨K₀, hK₀⟩ := exists_Q0_bound (N := N) (0 : Site (4 * h + 2)) μ h r
  have hK₀0 : 0 ≤ K₀ := (norm_nonneg _).trans (hK₀ 0 0 (by simp; exact hr.le) (by simp))
  refine ⟨r / 2, 4 * K / r ^ 2 + K₀ / r, by positivity, by positivity, fun {n} _ y X B hX => ?_⟩
  have hX0 : ‖refForm h X y‖ ≤ r / 2 := (norm_refForm_le h y X).trans hX
  have hA := agree_ref h (UX (N := N) X) B y
  rw [refConfig_UX] at hA
  rw [Qlin_reference hr hc y X (hX0.trans (by linarith)) B, Q0L_agree μ hA]
  refine (Q_sub_Q0_UX hr hc hK hK₀ hX0 _).trans ?_
  have hc0 : 0 ≤ 4 * K / r ^ 2 + K₀ / r := by positivity
  have h1 := mul_le_mul_of_nonneg_left (norm_refForm_le h y X) hc0
  exact mul_le_mul h1 (norm_refForm_le h y B) (norm_nonneg _) (mul_nonneg hc0 (norm_nonneg _))


/-- **`prop:relative-average`(v) for the core's `𝐔 = e^{iaA'}U`**: `‖La(Q(𝐔) - Q₀(𝐔))A‖ ≤ C₁(α₀ + α₁)‖aA‖_∞`, with
`c, C₁` depending on `L` and `G` only. -/
theorem relative_average_v (h : ℕ) (μ : Fin 4) :
    ∃ c C₁ : ℝ, 0 < c ∧ 0 ≤ C₁ ∧
      ∀ {n : ℕ} [NeZero n] (U : Config N n), U.IsGaugeField → 4 * h + 4 ≤ n → ∀ (y : Site n) (α₀ α₁ : ℝ),
        0 ≤ α₀ → 0 ≤ α₁ → α₀ ≤ c → α₁ ≤ c →
        (∀ μ' ν' z, PlaqIn (boxR y (loD h) (hiD h μ μ)) μ' ν' z →
          hs (((plaq U μ' ν' z : GLN) : Mat) - 1) ≤ α₀) →
        ∀ A' : Fin 4 → Site n → Mat, (∀ ρ z, BoxBond y h μ ρ z → ‖A' ρ z‖ ≤ α₁) →
        ∀ B : Fin 4 → Site n → Mat,
          ‖((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC U A') y μ h B - Q0L (moveC U A') y μ h B‖ ≤
            C₁ * (α₀ + α₁) * ‖B‖ := by
  obtain ⟨ci, hci, hpol⟩ := uniform_polydisc (N := N) h μ
  obtain ⟨r, C, hr, hC, hv⟩ := uniform_v (N := N) h μ
  set K := redK N h
  have hKpos : 0 < K := by linarith [four_le_redK N h]
  set m := min ci r with hm
  have hm0 : 0 < m := lt_min hci hr
  set c := min (m / (2 * K)) (1 / (8 * K)) with hc_def
  have hc1 : c ≤ m / (2 * K) := min_le_left _ _
  have hc2 : c ≤ 1 / (8 * K) := min_le_right _ _
  refine ⟨c, C * K, by positivity, by positivity, ?_⟩
  intro n _ U hU hn y α₀ α₁ hα₀ hα₁ hα₀c hα₁c hplq A' hA' B
  obtain ⟨X, hXn, hXa, hag⟩ := reduce_small hU hn y μ hα₀ hα₁ hα₀c hα₁c hc2 hplq A' hA'
  have hXm : ‖X‖ ≤ m / 2 := hXn.trans (by
    calc K * c ≤ K * (m / (2 * K)) := mul_le_mul_of_nonneg_left hc1 hKpos.le
      _ = m / 2 := by field_simp)
  have hXci : ‖X‖ < ci := lt_of_le_of_lt hXm (by have := min_le_left ci r; linarith)
  have hXr : ‖X‖ ≤ r := hXm.trans (by have := min_le_right ci r; linarith)
  have hn2 : 4 * h + 2 ≤ n := by omega
  have hpol' : ∀ X' B' : Fin 4 → Site n → Mat, ‖X'‖ < ci → ‖B'‖ < ci → Cond (N := N) y μ h (X', B') :=
    fun X' B' => hpol y X' B'
  set u := uG U y h
  set W := (moveC U A').gauge u
  have hu : ∀ z, ((u z : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ := fun z => hol_unitary' U hU _
  -- `Q₀(𝐔)B = Q₀(𝐔_X)Ad_uB`
  have hQ0 : Q0L (moveC U A') y μ h B = Q0L (UX (N := N) X) y μ h (AdF u B) := by
    have hg := Q0L_gauge W (fun z => (u z)⁻¹) y μ h (AdF u B)
    rw [gauge_gauge_inv, AdF_inv'] at hg
    have hw0 : (u y)⁻¹ = 1 := by simp only [u, uG_base U hn y, _root_.inv_one]
    rw [hg, hw0, Ad_one]
    rw [Q0L_local hn2 (V' := UX (N := N) X) fun ν z h1 h2 => hag ν z ⟨h1, h2⟩]
  rw [Qlin_reduce hU hn hag hci hpol' hXci, ContinuousLinearMap.comp_apply, AdFL_apply, hQ0]
  refine (hv y X (AdF u B) hXr).trans ?_
  rw [norm_AdF_unitary hu]
  have h1 : C * ‖X‖ ≤ C * (K * (α₀ + α₁)) := mul_le_mul_of_nonneg_left hXa hC
  calc C * ‖X‖ * ‖B‖ ≤ C * (K * (α₀ + α₁)) * ‖B‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = C * K * (α₀ + α₁) * ‖B‖ := by ring


/-! ### The dependence on the background -/

/-- **`Log` is Lipschitz near `id`**: `‖Log W - Log W'‖ ≤ 12‖W - W'‖` for `‖W - id‖, ‖W' - id‖ ≤ 1/2`. -/
theorem LogM_lip {W W' : Mat} (hW : ‖W - 1‖ ≤ 1 / 2) (hW' : ‖W' - 1‖ ≤ 1 / 2) :
    ‖LogM W - LogM W'‖ ≤ 12 * ‖W - W'‖ := by
  have hd : ∀ x ∈ ball (1 : Mat) (3 / 4), DifferentiableAt ℂ (LogM (N := N)) x := fun x hx => by
    rw [mem_ball, dist_eq_norm] at hx
    exact (analyticOnNhd_LogM (N := N) x (show ‖x - 1‖ < 1 by linarith)).differentiableAt
  have hK : ∀ x ∈ ball (1 : Mat) (3 / 4), ‖LogM x‖ ≤ 3 := fun x hx => by
    rw [mem_ball, dist_eq_norm] at hx
    have h1 : ‖x - 1‖ < 1 := by linarith
    have := BakerCampbellHausdorff.norm_log1p_le_div (𝕂 := ℂ) h1
    unfold LogM
    refine this.trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith [norm_nonneg (x - 1)]
  have hbd : ∀ x ∈ closedBall (1 : Mat) (1 / 2), ‖fderiv ℂ (LogM (N := N)) x‖ ≤ 12 := fun x hx => by
    rw [mem_closedBall, dist_eq_norm] at hx
    have hx' : x ∈ ball (1 : Mat) (3 / 4) := by rw [mem_ball, dist_eq_norm]; linarith
    refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun v => ?_
    have := SchwarzCauchy.cauchy_fderiv (fun y hy => (hd y hy).differentiableWithinAt) hK hx' v
    refine this.trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith [norm_nonneg v]
  have hmv := (convex_closedBall (1 : Mat) (1 / 2)).norm_image_sub_le_of_norm_fderiv_le
    (fun x hx => hd x (by rw [mem_closedBall, dist_eq_norm] at hx; rw [mem_ball, dist_eq_norm]; linarith))
    hbd (by rw [mem_closedBall, dist_eq_norm]; exact hW') (by rw [mem_closedBall, dist_eq_norm]; exact hW)
  exact hmv

/-- The box `B(c₋) ∪ B(c₊)` as a predicate on sites. -/
def InBoxB (y : Site n) (h : ℕ) (μ : Fin 4) (z : Site n) : Prop := Bm y h z ∨ Bp y h μ z

lemma restrictF_box_apply [DecidablePred (InBoxB y h μ)] (X : Fin 4 → Site n → Mat) {ρ : Fin 4} {z : Site n}
    (hb : BoxBond y h μ ρ z) : restrictF X (InBoxB y h μ) ρ z = X ρ z := by
  simp only [restrictF]; exact if_pos hb

lemma restrictF_box_apply' [DecidablePred (InBoxB y h μ)] (X : Fin 4 → Site n → Mat) {ρ : Fin 4} {z : Site n}
    (hb : ¬ BoxBond y h μ ρ z) : restrictF X (InBoxB y h μ) ρ z = 0 := by
  simp only [restrictF]; exact if_neg hb

/-- The reduction with the configuration supported on the box: `X` vanishes off the bonds of the box, and on them
`X = (1/i) Log 𝐔^u`. -/
theorem reduce_box_supp {h : ℕ} {U : Config N n} (hU : U.IsGaugeField) (hn : 4 * h + 4 ≤ n) (y : Site n)
    (μ : Fin 4) {α₀ α₁ c₀ : ℝ} (hα₀ : 0 ≤ α₀) (hα₁ : 0 ≤ α₁) (hα₀c : α₀ ≤ c₀) (hα₁c : α₁ ≤ c₀)
    (hc₀ : c₀ ≤ 1 / (8 * redK N h))
    (hplq : ∀ μ' ν' z, PlaqIn (boxR y (loD h) (hiD h μ μ)) μ' ν' z →
      hs (((plaq U μ' ν' z : GLN) : Mat) - 1) ≤ α₀)
    (A' : Fin 4 → Site n → Mat) (hA' : ∀ ρ z, BoxBond y h μ ρ z → ‖A' ρ z‖ ≤ α₁)
    [DecidablePred (InBoxB y h μ)] :
    ∃ X : Fin 4 → Site n → Mat, ‖X‖ ≤ redK N h * c₀ ∧ ‖X‖ ≤ redK N h * (α₀ + α₁) ∧
      (∀ ρ z, BoxBond y h μ ρ z → ((moveC U A').gauge (uG U y h)) ρ z = UX X ρ z) ∧
      (∀ ρ z, BoxBond y h μ ρ z →
        X ρ z = (1 / Complex.I) • LogM ((((moveC U A').gauge (uG U y h)) ρ z : GLN) : Mat)) ∧
      (∀ ρ z, ¬ BoxBond y h μ ρ z → X ρ z = 0) := by
  obtain ⟨X, hX1, hX2, hag⟩ := reduce_small hU hn y μ hα₀ hα₁ hα₀c hα₁c hc₀ hplq A' hA'
  have hKc : redK N h * c₀ ≤ 1 / 8 := by
    have hK := four_le_redK N h
    calc redK N h * c₀ ≤ redK N h * (1 / (8 * redK N h)) := mul_le_mul_of_nonneg_left hc₀ (by linarith)
      _ = 1 / 8 := by field_simp
  set Y := restrictF X (InBoxB y h μ)
  have hY : ‖Y‖ ≤ ‖X‖ := norm_restrictF_le X _
  refine ⟨Y, hY.trans hX1, hY.trans hX2, fun ρ z hb => ?_, fun ρ z hb => ?_,
    fun ρ z hb => restrictF_box_apply' X hb⟩
  · rw [hag ρ z hb]
    simp only [UX, moveC, Y, restrictF_box_apply X hb]
  · rw [hag ρ z hb]
    show restrictF X (InBoxB y h μ) ρ z = _
    rw [restrictF_box_apply X hb]
    have hXs : ‖Complex.I • X ρ z‖ < Real.log 2 := by
      rw [norm_I_smul']
      have := (norm_le_pi_norm (X ρ) z).trans (norm_le_pi_norm X ρ)
      have hl := Real.log_two_gt_d9
      linarith
    show X ρ z = (1 / Complex.I) • LogM ((expU (Complex.I • X ρ z) * (oneC (N := N) ρ z) : GLN) : Mat)
    simp only [oneC, mul_one]
    show X ρ z = (1 / Complex.I) • LogM (exp (Complex.I • X ρ z))
    rw [LogM_exp hXs, smul_smul, one_div, inv_mul_cancel₀ Complex.I_ne_zero, one_smul]


/-- **(vii) for `𝐔_X`, uniformly**: `‖L(Q(𝐔_{X₁}) - Q(𝐔_{X₂}))B‖ ≤ C‖X₁ - X₂‖‖B‖` for `‖X₁‖, ‖X₂‖ ≤ r`, on every
torus. -/
theorem uniform_vii (h : ℕ) (μ : Fin 4) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ∀ {n : ℕ} [NeZero n] (y : Site n) (X₁ X₂ B : Fin 4 → Site n → Mat),
      ‖X₁‖ ≤ r → ‖X₂‖ ≤ r →
      ‖((2 * h + 1 : ℕ) : ℂ) • Qlin (UX (N := N) X₁) y μ h B - ((2 * h + 1 : ℕ) : ℂ) • Qlin (UX (N := N) X₂) y μ h B‖
        ≤ C * ‖X₁ - X₂‖ * ‖B‖ := by
  obtain ⟨r, K, hr, hK0, hc, hK⟩ := bounds_UX (N := N) (n := 4 * h + 2) 0 μ h
  refine ⟨r / 2, 4 * K / r ^ 2, by positivity, by positivity, fun {n} _ y X₁ X₂ B h1 h2 => ?_⟩
  have h1' : ‖refForm h X₁ y‖ ≤ r / 2 := (norm_refForm_le h y X₁).trans h1
  have h2' : ‖refForm h X₂ y‖ ≤ r / 2 := (norm_refForm_le h y X₂).trans h2
  rw [Qlin_reference hr hc y X₁ (h1'.trans (by linarith)) B, Qlin_reference hr hc y X₂ (h2'.trans (by linarith)) B,
    ← smul_sub]
  refine (Qlin_lip_UX hr hc hK h1' h2' (refForm h B y)).trans ?_
  have e : refForm h X₁ y - refForm h X₂ y = refForm h (X₁ - X₂) y := rfl
  rw [e]
  have hc0 : 0 ≤ 4 * K / r ^ 2 := by positivity
  have h3 := mul_le_mul_of_nonneg_left (norm_refForm_le h y (X₁ - X₂)) hc0
  exact mul_le_mul h3 (norm_refForm_le h y B) (norm_nonneg _) (mul_nonneg hc0 (norm_nonneg _))

/-- The bonds of the box in the gauge `u`: `𝐔^u(b) = e^{iAd_{u(b₋)}aA'(b)}U^u(b)`. -/
lemma gauged_val (U : Config N n) (u : Site n → GLN) (A' : Fin 4 → Site n → Mat) (ρ : Fin 4) (z : Site n) :
    ((((moveC U A').gauge u) ρ z : GLN) : Mat) = exp (Complex.I • Ad (u z) (A' ρ z)) * (((U.gauge u) ρ z : GLN) : Mat) := by
  rw [← moveC_gauge]; rfl

/-- **The configurations of the reduction depend Lipschitz on `A'`**: `‖X₁ - X₂‖ ≤ 24‖a(A'₁ - A'₂)‖_{∞, box}`. -/
theorem X_lip {h : ℕ} {U : Config N n} (hU : U.IsGaugeField) (y : Site n) (μ : Fin 4)
    [DecidablePred (InBoxB y h μ)] {A'₁ A'₂ X₁ X₂ : Fin 4 → Site n → Mat}
    (hA₁ : ∀ ρ z, BoxBond y h μ ρ z → ‖A'₁ ρ z‖ ≤ 1 / 8) (hA₂ : ∀ ρ z, BoxBond y h μ ρ z → ‖A'₂ ρ z‖ ≤ 1 / 8)
    (hX₁ : ‖X₁‖ ≤ 1 / 8) (hX₂ : ‖X₂‖ ≤ 1 / 8)
    (hag₁ : ∀ ρ z, BoxBond y h μ ρ z → ((moveC U A'₁).gauge (uG U y h)) ρ z = UX X₁ ρ z)
    (hag₂ : ∀ ρ z, BoxBond y h μ ρ z → ((moveC U A'₂).gauge (uG U y h)) ρ z = UX X₂ ρ z)
    (hl₁ : ∀ ρ z, BoxBond y h μ ρ z →
      X₁ ρ z = (1 / Complex.I) • LogM ((((moveC U A'₁).gauge (uG U y h)) ρ z : GLN) : Mat))
    (hl₂ : ∀ ρ z, BoxBond y h μ ρ z →
      X₂ ρ z = (1 / Complex.I) • LogM ((((moveC U A'₂).gauge (uG U y h)) ρ z : GLN) : Mat))
    (hz₁ : ∀ ρ z, ¬ BoxBond y h μ ρ z → X₁ ρ z = 0) (hz₂ : ∀ ρ z, ¬ BoxBond y h μ ρ z → X₂ ρ z = 0) :
    ‖X₁ - X₂‖ ≤ 24 * ‖restrictF (A'₁ - A'₂) (InBoxB y h μ)‖ := by
  set u := uG U y h
  have hu : ∀ z, ((u z : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ := fun z => hol_unitary' U hU _
  have hUg : (U.gauge u).IsGaugeField := fun ρ z => by
    simp only [Config.gauge, Units.val_mul]
    exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (hu z) (hU ρ z)) (SupportCont.unitary_inv (hu _))
  -- the matrices of the bonds are close to `id`
  have hnear : ∀ (X : Fin 4 → Site n → Mat), ‖X‖ ≤ 1 / 8 → ∀ ρ z,
      ‖((UX (N := N) X ρ z : GLN) : Mat) - 1‖ ≤ 1 / 2 := fun X hX ρ z => by
    show ‖((expU (Complex.I • X ρ z) * oneC (N := N) ρ z : GLN) : Mat) - 1‖ ≤ 1 / 2
    simp only [oneC, mul_one]
    have hXz : ‖Complex.I • X ρ z‖ ≤ 1 / 8 := by
      rw [norm_I_smul']; exact ((norm_le_pi_norm (X ρ) z).trans (norm_le_pi_norm X ρ)).trans hX
    have := (BakerCampbellHausdorff.norm_exp_sub_one_le ℂ (Complex.I • X ρ z)).trans
      (exp_sub_one_le_two_mul (norm_nonneg _) hXz (by norm_num))
    show ‖exp (Complex.I • X ρ z) - 1‖ ≤ 1 / 2
    linarith
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun ρ => (pi_norm_le_iff_of_nonneg (by positivity)).2
    fun z => ?_
  rw [Pi.sub_apply, Pi.sub_apply]
  by_cases hb : BoxBond y h μ ρ z
  · rw [hl₁ ρ z hb, hl₂ ρ z hb, ← smul_sub, norm_smul, one_div, norm_inv, Complex.norm_I, _root_.inv_one, one_mul]
    have hW1 := hnear X₁ hX₁ ρ z
    have hW2 := hnear X₂ hX₂ ρ z
    rw [← hag₁ ρ z hb] at hW1
    rw [← hag₂ ρ z hb] at hW2
    refine (LogM_lip hW1 hW2).trans ?_
    rw [gauged_val, gauged_val, ← sub_mul, CStarRing.norm_mul_mem_unitary _ (hUg ρ z)]
    have ha1 : ‖Complex.I • Ad (u z) (A'₁ ρ z)‖ ≤ 1 / 8 := by
      rw [norm_I_smul', SupportCont.opNorm_Ad_unitary (hu z)]; exact hA₁ ρ z hb
    have ha2 : ‖Complex.I • Ad (u z) (A'₂ ρ z)‖ ≤ 1 / 8 := by
      rw [norm_I_smul', SupportCont.opNorm_Ad_unitary (hu z)]; exact hA₂ ρ z hb
    have hE := norm_exp_sub_exp_le norm_one_mat_le ha1 ha2
    rw [← smul_sub, norm_I_smul', ← Ad_sub, SupportCont.opNorm_Ad_unitary (hu z)] at hE
    have hexp : Real.exp (1 / 8) ≤ 2 := by
      have := exp_sub_one_le_two_mul (a := 1 / 8) (t := 1 / 8) (by norm_num) le_rfl (by norm_num)
      linarith
    have hr : ‖A'₁ ρ z - A'₂ ρ z‖ ≤ ‖restrictF (A'₁ - A'₂) (InBoxB y h μ)‖ := by
      have := (norm_le_pi_norm (restrictF (A'₁ - A'₂) (InBoxB y h μ) ρ) z).trans
        (norm_le_pi_norm (restrictF (A'₁ - A'₂) (InBoxB y h μ)) ρ)
      rwa [restrictF_box_apply _ hb] at this
    have h0 : 0 ≤ ‖A'₁ ρ z - A'₂ ρ z‖ := norm_nonneg _
    nlinarith [Real.exp_pos (1 / 8)]
  · rw [hz₁ ρ z hb, hz₂ ρ z hb, sub_zero, norm_zero]; positivity

/-- **`prop:relative-average`(vii) for the core's `𝐔`**: `‖La(Q(e^{iaA'₁}U) - Q(e^{iaA'₂}U))A‖ ≤
C₁‖a(A'₁ - A'₂)‖_{∞,box}‖aA‖_∞`, with `c, C₁` depending on `L` and `G` only. -/
theorem relative_average_vii (h : ℕ) (μ : Fin 4) :
    ∃ c C₁ : ℝ, 0 < c ∧ 0 ≤ C₁ ∧
      ∀ {n : ℕ} [NeZero n] (U : Config N n), U.IsGaugeField → 4 * h + 4 ≤ n → ∀ (y : Site n)
        [DecidablePred (InBoxB y h μ)] (α₀ α₁ : ℝ), 0 ≤ α₀ → 0 ≤ α₁ → α₀ ≤ c → α₁ ≤ c →
        (∀ μ' ν' z, PlaqIn (boxR y (loD h) (hiD h μ μ)) μ' ν' z →
          hs (((plaq U μ' ν' z : GLN) : Mat) - 1) ≤ α₀) →
        ∀ A'₁ A'₂ : Fin 4 → Site n → Mat, (∀ ρ z, BoxBond y h μ ρ z → ‖A'₁ ρ z‖ ≤ α₁) →
        (∀ ρ z, BoxBond y h μ ρ z → ‖A'₂ ρ z‖ ≤ α₁) → ∀ B : Fin 4 → Site n → Mat,
          ‖((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC U A'₁) y μ h B - ((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC U A'₂) y μ h B‖
            ≤ C₁ * ‖restrictF (A'₁ - A'₂) (InBoxB y h μ)‖ * ‖B‖ := by
  obtain ⟨ci, hci, hpol⟩ := uniform_polydisc (N := N) h μ
  obtain ⟨r, C, hr, hC, hlip⟩ := uniform_vii (N := N) h μ
  set K := redK N h
  have hK4 : 4 ≤ K := four_le_redK N h
  have hKpos : 0 < K := by linarith
  set m := min ci r with hm
  have hm0 : 0 < m := lt_min hci hr
  set c := min (m / (2 * K)) (1 / (8 * K)) with hc_def
  have hc1 : c ≤ m / (2 * K) := min_le_left _ _
  have hc2 : c ≤ 1 / (8 * K) := min_le_right _ _
  refine ⟨c, 24 * C, by positivity, by positivity, ?_⟩
  intro n _ U hU hn y _ α₀ α₁ hα₀ hα₁ hα₀c hα₁c hplq A'₁ A'₂ hA₁ hA₂ B
  obtain ⟨X₁, hX1c, -, hag₁, hl₁, hz₁⟩ := reduce_box_supp hU hn y μ hα₀ hα₁ hα₀c hα₁c hc2 hplq A'₁ hA₁
  obtain ⟨X₂, hX2c, -, hag₂, hl₂, hz₂⟩ := reduce_box_supp hU hn y μ hα₀ hα₁ hα₀c hα₁c hc2 hplq A'₂ hA₂
  have hKc : K * c ≤ m / 2 := by
    calc K * c ≤ K * (m / (2 * K)) := mul_le_mul_of_nonneg_left hc1 hKpos.le
      _ = m / 2 := by field_simp
  have hK8 : K * c ≤ 1 / 8 := by
    calc K * c ≤ K * (1 / (8 * K)) := mul_le_mul_of_nonneg_left hc2 hKpos.le
      _ = 1 / 8 := by field_simp
  have hmci : m ≤ ci := min_le_left _ _
  have hmr : m ≤ r := min_le_right _ _
  have hpol' : ∀ X' B' : Fin 4 → Site n → Mat, ‖X'‖ < ci → ‖B'‖ < ci → Cond (N := N) y μ h (X', B') :=
    fun X' B' => hpol y X' B'
  have hu : ∀ z, ((uG U y h z : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ := fun z => hol_unitary' U hU _
  have hc8 : c ≤ 1 / 8 := hc2.trans (by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith)
  rw [Qlin_reduce hU hn hag₁ hci hpol' (by linarith), Qlin_reduce hU hn hag₂ hci hpol' (by linarith),
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, AdFL_apply]
  refine (hlip y X₁ X₂ _ (by linarith) (by linarith)).trans ?_
  rw [norm_AdF_unitary hu]
  have hXl := X_lip hU y μ (fun ρ z hb => (hA₁ ρ z hb).trans (hα₁c.trans hc8))
    (fun ρ z hb => (hA₂ ρ z hb).trans (hα₁c.trans hc8)) (by linarith) (by linarith) hag₁ hag₂ hl₁ hl₂ hz₁ hz₂
  have h1 : C * ‖X₁ - X₂‖ ≤ C * (24 * ‖restrictF (A'₁ - A'₂) (InBoxB y h μ)‖) := mul_le_mul_of_nonneg_left hXl hC
  calc C * ‖X₁ - X₂‖ * ‖B‖ ≤ C * (24 * ‖restrictF (A'₁ - A'₂) (InBoxB y h μ)‖) * ‖B‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = 24 * C * ‖restrictF (A'₁ - A'₂) (InBoxB y h μ)‖ * ‖B‖ := by ring


/-! ### The norms over the box -/

/-- The restriction of a form to the bonds of the box, as a continuous linear map. -/
def restrictBoxL (y : Site n) (h : ℕ) (μ : Fin 4) [DecidablePred (InBoxB y h μ)] :
    (Fin 4 → Site n → Mat) →L[ℂ] (Fin 4 → Site n → Mat) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun B => restrictF B (InBoxB y h μ)
      map_add' := fun B B' => by funext ν z; simp only [restrictF, Pi.add_apply]; split_ifs <;> simp
      map_smul' := fun c B => by funext ν z; simp only [restrictF, Pi.smul_apply]; split_ifs <;> simp }

@[simp] lemma restrictBoxL_apply (y : Site n) (h : ℕ) (μ : Fin 4) [DecidablePred (InBoxB y h μ)]
    (B : Fin 4 → Site n → Mat) : restrictBoxL y h μ B = restrictF B (InBoxB y h μ) := rfl

/-- **`(1/i) log 𝓜_𝐔(A)(c)` depends only on the values of `aA` on the bonds of the box.** -/
lemma relLog_box {h : ℕ} (hn : 4 * h + 2 ≤ n) (V : Config N n) (y : Site n) (μ : Fin 4)
    [DecidablePred (InBoxB y h μ)] (B : Fin 4 → Site n → Mat) :
    relLog V B y μ h = relLog V (restrictF B (InBoxB y h μ)) y μ h := by
  simp only [relLog]
  rw [relAvg_local hn fun ν z h1 h2 => ⟨rfl, (restrictF_box_apply B ⟨h1, h2⟩).symm⟩]

/-- **`Q(𝐔)` depends only on the values on the box**, where `B ↦ (1/i) log 𝓜_𝐔(B)` is differentiable at `0`. -/
lemma Qlin_box {h : ℕ} (hn : 4 * h + 2 ≤ n) (V : Config N n) (y : Site n) (μ : Fin 4)
    [DecidablePred (InBoxB y h μ)] (hd : DifferentiableAt ℂ (fun B => relLog V B y μ h) 0) :
    Qlin V y μ h = (Qlin V y μ h).comp (restrictBoxL y h μ) := by
  have e : (fun B => relLog V B y μ h) = (fun B => relLog V B y μ h) ∘ restrictBoxL y h μ := by
    funext B; exact relLog_box hn V y μ B
  have hd' : DifferentiableAt ℂ (fun B => relLog V B y μ h) (restrictBoxL y h μ 0) := by
    rw [map_zero]; exact hd
  have hfd : fderiv ℂ (fun B => relLog V B y μ h) 0 =
      (fderiv ℂ (fun B => relLog V B y μ h) 0).comp (restrictBoxL y h μ) := by
    conv_lhs => rw [e]
    rw [fderiv_comp 0 hd' (restrictBoxL y h μ).differentiableAt, (restrictBoxL y h μ).fderiv, map_zero]
  simp only [Qlin]
  conv_lhs => rw [hfd]
  rw [ContinuousLinearMap.smul_comp]

/-- The bonds at which `Q₀` evaluates the form lie in the box. -/
lemma eval_box {h : ℕ} (hn : 4 * h + 2 ≤ n) (y : Site n) (μ : Fin 4) (x : Pts h) {j : ℕ} (hj : j < 2 * h + 1) :
    BoxBond y h μ μ (ofs y (offP h x) + j • unit n μ) := by
  have hc := offP_inM h x
  have hbx : ∀ i : ℕ, i ≤ 2 * h + 1 → InBoxB y h μ (ofs y (offP h x + Pi.single μ (i : ℤ))) := fun i hi => by
    by_cases hi' : (offP h x μ) + i ≤ h
    · left
      refine bm_ofs hn fun σ => ?_
      have := hc σ
      simp only [Pi.add_apply, Pi.single_apply]
      split_ifs with hσ
      · subst hσ; constructor <;> omega
      · simpa using this
    · right
      refine bp_ofs hn fun σ => ⟨fun hσ => ?_, fun hσ => ?_⟩
      · have := hc σ
        simp only [Pi.add_apply, Pi.single_apply, if_neg hσ, add_zero]; exact this
      · subst hσ
        have := hc σ
        simp only [Pi.add_apply, Pi.single_apply, if_true]
        constructor <;> omega
  constructor
  · rw [ofs_add_nsmul]; exact hbx j hj.le
  · rw [ofs_add_nsmul, ← ofs1]
    have : offP h x + Pi.single μ (j : ℤ) + Pi.single μ 1 = offP h x + Pi.single μ ((j + 1 : ℕ) : ℤ) := by
      funext σ; simp only [Pi.add_apply, Pi.single_apply]; split_ifs <;> push_cast <;> ring
    rw [this]; exact hbx (j + 1) hj

/-- **`Q₀(𝐔)` depends only on the values on the box.** -/
lemma Q0L_box {h : ℕ} (hn : 4 * h + 2 ≤ n) (V : Config N n) (y : Site n) (μ : Fin 4)
    [DecidablePred (InBoxB y h μ)] (B : Fin 4 → Site n → Mat) :
    Q0L V y μ h B = Q0L V y μ h (restrictF B (InBoxB y h μ)) := by
  have hx : ∀ x : Pts h, (∑ Γ : Ords (offP h x), ∑ j ∈ Finset.range (2 * h + 1),
      Ad (V.hol (pathGb y μ h x Γ j)) (B μ (ofs y (offP h x) + j • unit n μ))) =
      ∑ Γ : Ords (offP h x), ∑ j ∈ Finset.range (2 * h + 1),
      Ad (V.hol (pathGb y μ h x Γ j)) (restrictF B (InBoxB y h μ) μ (ofs y (offP h x) + j • unit n μ)) :=
    fun x => Finset.sum_congr rfl fun Γ _ => Finset.sum_congr rfl fun j hj => by
      rw [restrictF_box_apply B (eval_box hn y μ x (Finset.mem_range.1 hj))]
  simp only [Q0L, ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.comp_apply, AdL_apply, evalL_apply, hx]

lemma norm_restrict_AdF {u : Site n → GLN} (hu : ∀ z, ((u z : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ)
    (y : Site n) (h : ℕ) (μ : Fin 4) [DecidablePred (InBoxB y h μ)] (B : Fin 4 → Site n → Mat) :
    ‖AdF u (restrictF B (InBoxB y h μ))‖ = ‖restrictF B (InBoxB y h μ)‖ := norm_AdF_unitary hu _

/-- **(v) and (vi) for the core's `𝐔`, in the norms over the box**: with `‖aA‖_{∞,box}` the supremum over the
bonds with both ends in `B(c₋) ∪ B(c₊)`, `‖La(Q - Q₀)A‖ ≤ C₁(α₀ + α₁)‖aA‖_{∞,box}`, `‖LaQA‖ ≤ C₁‖aA‖_{∞,box}`, and,
for `‖aA‖_{∞,box} < c`, `‖C(𝐔; aA)‖ ≤ C₂‖aA‖²_{∞,box}` and `‖DC(𝐔; aA)δ‖ ≤ C₃‖aA‖_{∞,box}‖δ‖_{∞,box}`. -/
theorem relative_average_box (h : ℕ) (μ : Fin 4) :
    ∃ c C₀ C₁ C₂ C₃ : ℝ, 0 < c ∧ 0 ≤ C₀ ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ 0 ≤ C₃ ∧
      ∀ {n : ℕ} [NeZero n] (U : Config N n), U.IsGaugeField → 4 * h + 4 ≤ n → ∀ (y : Site n)
        [DecidablePred (InBoxB y h μ)] (α₀ α₁ : ℝ), 0 ≤ α₀ → 0 ≤ α₁ → α₀ ≤ c → α₁ ≤ c →
        (∀ μ' ν' z, PlaqIn (boxR y (loD h) (hiD h μ μ)) μ' ν' z →
          hs (((plaq U μ' ν' z : GLN) : Mat) - 1) ≤ α₀) →
        ∀ A' : Fin 4 → Site n → Mat, (∀ ρ z, BoxBond y h μ ρ z → ‖A' ρ z‖ ≤ α₁) →
        ∀ B : Fin 4 → Site n → Mat,
          ‖((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC U A') y μ h B - Q0L (moveC U A') y μ h B‖ ≤
            C₀ * (α₀ + α₁) * ‖restrictF B (InBoxB y h μ)‖ ∧
          ‖((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC U A') y μ h B‖ ≤ C₁ * ‖restrictF B (InBoxB y h μ)‖ ∧
          (‖restrictF B (InBoxB y h μ)‖ < c →
            ‖Crem (moveC U A') B y μ h‖ ≤ C₂ * ‖restrictF B (InBoxB y h μ)‖ ^ 2 ∧
            ∀ δ, ‖fderiv ℂ (fun B' => Crem (moveC U A') B' y μ h) B δ‖ ≤
              C₃ * ‖restrictF B (InBoxB y h μ)‖ * ‖restrictF δ (InBoxB y h μ)‖) := by
  obtain ⟨cv, C₀, hcv, hC₀, hv⟩ := relative_average_v (N := N) h μ
  obtain ⟨ci, hci, hpol⟩ := uniform_polydisc (N := N) h μ
  obtain ⟨cvi, C₁, C₂, C₃, hcvi, hC₁, hC₂, hC₃, hvi⟩ := relative_average_vi (N := N) h μ
  -- a common smallness for the polydisc of the transport
  set K := redK N h
  have hKpos : 0 < K := by linarith [four_le_redK N h]
  set c := min (min cv cvi) (min (ci / (2 * K)) (1 / (8 * K))) with hc_def
  have hc0 : 0 < c := lt_min (lt_min hcv hcvi) (lt_min (by positivity) (by positivity))
  have hccv : c ≤ cv := (min_le_left _ _).trans (min_le_left _ _)
  have hccvi : c ≤ cvi := (min_le_left _ _).trans (min_le_right _ _)
  have hcci : c ≤ ci / (2 * K) := (min_le_right _ _).trans (min_le_left _ _)
  have hc8 : c ≤ 1 / (8 * K) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨c, C₀, C₁, C₂, C₃, hc0, hC₀, hC₁, hC₂, hC₃, ?_⟩
  intro n _ U hU hn y _ α₀ α₁ hα₀ hα₁ hα₀c hα₁c hplq A' hA' B
  have hn2 : 4 * h + 2 ≤ n := by omega
  set R := restrictBoxL (N := N) y h μ
  set V := moveC U A'
  -- the reduction, for the locality in `B`
  obtain ⟨X, hXn, -, hag⟩ := reduce_small hU hn y μ hα₀ hα₁ hα₀c hα₁c hc8 hplq A' hA'
  have hXci : ‖X‖ < ci := by
    have : K * c ≤ ci / 2 := by
      calc K * c ≤ K * (ci / (2 * K)) := mul_le_mul_of_nonneg_left hcci hKpos.le
        _ = ci / 2 := by field_simp
    linarith
  have hpol' : ∀ X' B' : Fin 4 → Site n → Mat, ‖X'‖ < ci → ‖B'‖ < ci → Cond (N := N) y μ h (X', B') :=
    fun X' B' => hpol y X' B'
  have hu : ∀ z, ((uG U y h z : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ := fun z => hol_unitary' U hU _
  -- `Q(𝐔) = Q(𝐔)R`
  have hdX : DifferentiableAt ℂ (fun B' => relLog (UX (N := N) X) B' y μ h) 0 :=
    (relLog_pair_differentiableAt (hpol' X 0 hXci (by rw [norm_zero]; exact hci))).comp
      (f := fun B' : Fin 4 → Site n → Mat => ((X, B') : PairSp N n)) 0
      ((differentiableAt_const X).prodMk differentiableAt_id)
  have hXR : ∀ B'', Qlin (UX (N := N) X) y μ h B'' = Qlin (UX (N := N) X) y μ h (R B'') := fun B'' => by
    conv_lhs => rw [Qlin_box hn2 _ y μ hdX]
    rfl
  have hQR : ∀ B', Qlin V y μ h B' = Qlin V y μ h (R B') := fun B' => by
    rw [Qlin_reduce hU hn hag hci hpol' hXci, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      AdFL_apply, AdFL_apply, hXR (AdF (uG U y h) B'), restrictBoxL_apply, restrictF_AdF]
    rfl
  have hCR : ∀ B', Crem V B' y μ h = Crem V (R B') y μ h := fun B' => by
    unfold Crem; rw [relLog_box hn2 V y μ B', hQR B']; rfl
  have hRR : R (R B) = R B := restrictF_restrictF B _
  have hRn : ‖R (R B)‖ = ‖R B‖ := by rw [hRR]
  obtain ⟨hlin, hrem, hder⟩ := hvi U hU hn y α₀ α₁ hα₀ hα₁ (hα₀c.trans hccvi) (hα₁c.trans hccvi) hplq A' hA' (R B)
  refine ⟨?_, ?_, fun hB => ⟨?_, fun δ => ?_⟩⟩
  · rw [hQR B, Q0L_box hn2 V y μ B]
    exact hv U hU hn y α₀ α₁ hα₀ hα₁ (hα₀c.trans hccv) (hα₁c.trans hccv) hplq A' hA' (R B)
  · rw [hQR B]; exact hlin
  · rw [hCR B]; exact hrem (lt_of_lt_of_le hB hccvi)
  · -- the derivative through the restriction
    have hRB : ‖R B‖ < cvi := lt_of_lt_of_le hB hccvi
    have hRBci : ‖R B‖ < ci := lt_of_lt_of_le hB (hcci.trans (by
      rw [div_le_iff₀ (by positivity)]; nlinarith [four_le_redK N h]))
    have heq : (fun B' => Crem V B' y μ h) = (fun B' => Crem V B' y μ h) ∘ R := by
      funext B'; exact hCR B'
    have hdR : DifferentiableAt ℂ (fun B' => Crem V B' y μ h) (R B) := by
      have hloc : (fun B' => Crem V B' y μ h) =ᶠ[𝓝 (R B)]
          (fun B' => Crem (UX (N := N) X) B' y μ h) ∘ AdFL (uG U y h) := by
        filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hRBci)] with B' hB'
        rw [mem_ball_zero_iff] at hB'
        simp only [Function.comp_apply, AdFL_apply]
        exact Crem_reduce hU hn hag hci hpol' hXci B' hB'
      refine DifferentiableAt.congr_of_eventuallyEq ?_ hloc
      refine DifferentiableAt.comp (R B) ?_ (AdFL (uG U y h)).differentiableAt
      have hdC : DifferentiableOn ℂ (fun B' => Crem (UX (N := N) X) B' y μ h) (ball 0 ci) := by
        unfold Crem
        refine DifferentiableOn.sub (fun B' hB' => ?_)
          ((((2 * h + 1 : ℕ) : ℂ) • Qlin (UX (N := N) X) y μ h).differentiable.differentiableOn)
        rw [mem_ball_zero_iff] at hB'
        exact ((relLog_pair_differentiableAt (hpol' X B' hXci hB')).comp
          (f := fun B'' : Fin 4 → Site n → Mat => ((X, B'') : PairSp N n)) B'
          ((differentiableAt_const X).prodMk differentiableAt_id)).differentiableWithinAt
      rw [AdFL_apply]
      exact hdC.differentiableAt (isOpen_ball.mem_nhds (by
        rw [mem_ball_zero_iff, norm_AdF_unitary hu]; exact hRBci))
    rw [heq, fderiv_comp B (by rw [show R B = R B from rfl]; exact hdR) R.differentiableAt, R.fderiv,
      ContinuousLinearMap.comp_apply]
    exact hder hRB (R δ)


/-- **`Q(𝐔)A` depends only on the values of `aA` on the box**, for the core's `𝐔` in the reduction. -/
theorem Qlin_restrict {U : Config N n} {h : ℕ} {y : Site n} {μ : Fin 4} {A' X : Fin 4 → Site n → Mat}
    [DecidablePred (InBoxB y h μ)] (hU : U.IsGaugeField) (hn : 4 * h + 4 ≤ n)
    (hag : ∀ ρ z, BoxBond y h μ ρ z → ((moveC U A').gauge (uG U y h)) ρ z = UX X ρ z)
    {ci : ℝ} (hci : 0 < ci)
    (hpol : ∀ X' B' : Fin 4 → Site n → Mat, ‖X'‖ < ci → ‖B'‖ < ci → Cond (N := N) y μ h (X', B'))
    (hX : ‖X‖ < ci) (B : Fin 4 → Site n → Mat) :
    Qlin (moveC U A') y μ h B = Qlin (moveC U A') y μ h (restrictF B (InBoxB y h μ)) := by
  have hn2 : 4 * h + 2 ≤ n := by omega
  have hdX : DifferentiableAt ℂ (fun B' => relLog (UX (N := N) X) B' y μ h) 0 :=
    (relLog_pair_differentiableAt (hpol X 0 hX (by rw [norm_zero]; exact hci))).comp
      (f := fun B' : Fin 4 → Site n → Mat => ((X, B') : PairSp N n)) 0
      ((differentiableAt_const X).prodMk differentiableAt_id)
  have hXR : ∀ B'', Qlin (UX (N := N) X) y μ h B'' =
      Qlin (UX (N := N) X) y μ h (restrictBoxL y h μ B'') := fun B'' => by
    conv_lhs => rw [Qlin_box hn2 _ y μ hdX]
    rfl
  rw [Qlin_reduce hU hn hag hci hpol hX, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    AdFL_apply, AdFL_apply, hXR (AdF (uG U y h) B), restrictBoxL_apply, restrictF_AdF]

/-- **(vii) for the core's `𝐔`, in the norms of (v)**: `‖La(Q(e^{iaA'₁}U) - Q(e^{iaA'₂}U))A‖ ≤
C₁‖a(A'₁ - A'₂)‖_{∞,box}‖aA‖_{∞,box}`. -/
theorem relative_average_vii_box (h : ℕ) (μ : Fin 4) :
    ∃ c C₁ : ℝ, 0 < c ∧ 0 ≤ C₁ ∧
      ∀ {n : ℕ} [NeZero n] (U : Config N n), U.IsGaugeField → 4 * h + 4 ≤ n → ∀ (y : Site n)
        [DecidablePred (InBoxB y h μ)] (α₀ α₁ : ℝ), 0 ≤ α₀ → 0 ≤ α₁ → α₀ ≤ c → α₁ ≤ c →
        (∀ μ' ν' z, PlaqIn (boxR y (loD h) (hiD h μ μ)) μ' ν' z →
          hs (((plaq U μ' ν' z : GLN) : Mat) - 1) ≤ α₀) →
        ∀ A'₁ A'₂ : Fin 4 → Site n → Mat, (∀ ρ z, BoxBond y h μ ρ z → ‖A'₁ ρ z‖ ≤ α₁) →
        (∀ ρ z, BoxBond y h μ ρ z → ‖A'₂ ρ z‖ ≤ α₁) → ∀ B : Fin 4 → Site n → Mat,
          ‖((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC U A'₁) y μ h B - ((2 * h + 1 : ℕ) : ℂ) • Qlin (moveC U A'₂) y μ h B‖
            ≤ C₁ * ‖restrictF (A'₁ - A'₂) (InBoxB y h μ)‖ * ‖restrictF B (InBoxB y h μ)‖ := by
  obtain ⟨c7, C₁, hc7, hC₁, h7⟩ := relative_average_vii (N := N) h μ
  obtain ⟨ci, hci, hpol⟩ := uniform_polydisc (N := N) h μ
  set K := redK N h
  have hKpos : 0 < K := by linarith [four_le_redK N h]
  set c := min c7 (min (ci / (2 * K)) (1 / (8 * K))) with hc_def
  have hc0 : 0 < c := lt_min hc7 (lt_min (by positivity) (by positivity))
  have hc7' : c ≤ c7 := min_le_left _ _
  have hcci : c ≤ ci / (2 * K) := (min_le_right _ _).trans (min_le_left _ _)
  have hc8 : c ≤ 1 / (8 * K) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨c, C₁, hc0, hC₁, ?_⟩
  intro n _ U hU hn y _ α₀ α₁ hα₀ hα₁ hα₀c hα₁c hplq A'₁ A'₂ hA₁ hA₂ B
  have hKc : K * c < ci := by
    have : K * c ≤ ci / 2 := by
      calc K * c ≤ K * (ci / (2 * K)) := mul_le_mul_of_nonneg_left hcci hKpos.le
        _ = ci / 2 := by field_simp
    linarith
  have hpol' : ∀ X' B' : Fin 4 → Site n → Mat, ‖X'‖ < ci → ‖B'‖ < ci → Cond (N := N) y μ h (X', B') :=
    fun X' B' => hpol y X' B'
  obtain ⟨X₁, hX₁, -, hag₁⟩ := reduce_small hU hn y μ hα₀ hα₁ hα₀c hα₁c hc8 hplq A'₁ hA₁
  obtain ⟨X₂, hX₂, -, hag₂⟩ := reduce_small hU hn y μ hα₀ hα₁ hα₀c hα₁c hc8 hplq A'₂ hA₂
  rw [Qlin_restrict hU hn hag₁ hci hpol' (by linarith) B, Qlin_restrict hU hn hag₂ hci hpol' (by linarith) B]
  exact h7 U hU hn y α₀ α₁ hα₀ hα₁ (hα₀c.trans hc7') (hα₁c.trans hc7') hplq A'₁ A'₂ hA₁ hA₂ _


/-! ### The block average `Q'` -/

lemma blockAvg_X_differentiableAt {h : ℕ} {y : Site n} (lam : Site n → Mat) {X₀ : Fin 4 → Site n → Mat}
    (hg : GoodAt (UX (N := N) X₀) y h) :
    DifferentiableAt ℂ (fun X => blockAvg (UX (N := N) X) lam y h) X₀ := by
  have ht : ∀ x : Pts h, DifferentiableAt ℂ (fun X => ((trans (UX (N := N) X) y h x : GLN) : Mat)) X₀ :=
    fun x => trans_differentiableAt (fun X => UX (N := N) X) (fun μ z => moveC_differentiableAt oneC X₀ μ z)
      y h x (hg.1 x) ((hg.2 x).trans (by norm_num))
  simp only [blockAvg, Ad]
  apply DifferentiableAt.fun_const_smul
  apply DifferentiableAt.fun_sum
  intro x _
  exact ((ht x).mul_const _).mul (inv_differentiableAt (ht x))

lemma blockAvg_pair_differentiableAt {h : ℕ} {y : Site n} (p : (Fin 4 → Site n → Mat) × (Site n → Mat))
    (hg : GoodAt (UX (N := N) p.1) y h) :
    DifferentiableAt ℂ (fun q : (Fin 4 → Site n → Mat) × (Site n → Mat) => blockAvg (UX (N := N) q.1) q.2 y h) p := by
  have ht : ∀ x : Pts h, DifferentiableAt ℂ (fun q : (Fin 4 → Site n → Mat) × (Site n → Mat) =>
      ((trans (UX (N := N) q.1) y h x : GLN) : Mat)) p := fun x =>
    trans_differentiableAt (fun q : (Fin 4 → Site n → Mat) × (Site n → Mat) => UX (N := N) q.1)
      (fun μ z => (moveC_differentiableAt oneC p.1 μ z).comp p differentiableAt_fst)
      y h x (hg.1 x) ((hg.2 x).trans (by norm_num))
  have hl : ∀ x : Pts h, DifferentiableAt ℂ (fun q : (Fin 4 → Site n → Mat) × (Site n → Mat) =>
      q.2 (ofs y (offP h x))) p := fun x =>
    (differentiableAt_pi.1 differentiableAt_snd) _
  simp only [blockAvg, Ad]
  apply DifferentiableAt.fun_const_smul
  apply DifferentiableAt.fun_sum
  intro x _
  exact ((ht x).mul (hl x)).mul (inv_differentiableAt (ht x))

/-- `Q'(𝐔_X)` is Lipschitz in `X` on the polydisc, uniformly in the `0`-form of norm at most `1`. -/
theorem blockAvg_lip_UX {y : Site n} {μ : Fin 4} {h : ℕ} {r : ℝ} (hr : 0 < r)
    (hc : ∀ X B : Fin 4 → Site n → Mat, ‖X‖ ≤ r → ‖B‖ ≤ r → Cond (N := N) y μ h (X, B)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (lam : Site n → Mat) (X₁ X₂ : Fin 4 → Site n → Mat), ‖X₁‖ ≤ r / 2 → ‖X₂‖ ≤ r / 2 →
      ‖blockAvg (UX (N := N) X₁) lam y h - blockAvg (UX (N := N) X₂) lam y h‖ ≤ C * ‖X₁ - X₂‖ * ‖lam‖ := by
  have hg : ∀ X : Fin 4 → Site n → Mat, ‖X‖ ≤ r → GoodAt (UX (N := N) X) y h := fun X hX =>
    (hc X 0 hX (by rw [norm_zero]; exact hr.le)).g0
  -- the bound on the compact set of the pairs `(X, λ)`, `‖X‖ ≤ r`, `‖λ‖ ≤ 1`
  have hcont : ContinuousOn (fun p : (Fin 4 → Site n → Mat) × (Site n → Mat) => blockAvg (UX (N := N) p.1) p.2 y h)
      (Metric.closedBall 0 r ×ˢ Metric.closedBall 0 1) := by
    intro p hp
    have hX : ‖p.1‖ ≤ r := by have := hp.1; rwa [mem_closedBall, dist_zero_right] at this
    exact (blockAvg_pair_differentiableAt p (hg _ hX)).continuousAt.continuousWithinAt
  obtain ⟨K, hK⟩ := ((isCompact_closedBall (0 : Fin 4 → Site n → Mat) r).prod
    (isCompact_closedBall (0 : Site n → Mat) 1)).exists_bound_of_continuousOn hcont
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK ((0, 0) : (Fin 4 → Site n → Mat) × (Site n → Mat))
    ⟨by simp [hr.le], by simp⟩)
  refine ⟨2 * K / r, by positivity, fun lam X₁ X₂ h1 h2 => ?_⟩
  -- reduce to `‖λ‖ = 1`
  rcases eq_or_ne lam 0 with rfl | hl
  · simp [blockAvg, Ad]
  have hlp : 0 < ‖lam‖ := norm_pos_iff.2 hl
  set lam' := (‖lam‖⁻¹ : ℂ) • lam with hlam'
  have hl'n : ‖lam'‖ = 1 := by
    rw [hlam', norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hlp.le, inv_mul_cancel₀ hlp.ne']
  have hlin : ∀ X : Fin 4 → Site n → Mat, blockAvg (UX (N := N) X) lam y h =
      (‖lam‖ : ℂ) • blockAvg (UX (N := N) X) lam' y h := fun X => by
    have e : lam = (‖lam‖ : ℂ) • lam' := by
      rw [hlam', smul_smul, mul_inv_cancel₀ (by exact_mod_cast hlp.ne'), one_smul]
    conv_lhs => rw [e]
    simp only [blockAvg, Pi.smul_apply, Ad_smul, ← Finset.smul_sum, smul_comm (((2 * h + 1 : ℕ) : ℂ) ^ 4)⁻¹]
  -- the Lipschitz bound in `X` for `λ'`
  have hd : DifferentiableOn ℂ (fun X => blockAvg (UX (N := N) X) lam' y h) (ball 0 r) := fun X hX =>
    (blockAvg_X_differentiableAt lam' (hg X (by rw [mem_ball, dist_zero_right] at hX; exact hX.le))).differentiableWithinAt
  have hsub : closedBall (0 : Fin 4 → Site n → Mat) (r / 2) ⊆ ball 0 r := closedBall_subset_ball (by linarith)
  have hder : ∀ X ∈ closedBall (0 : Fin 4 → Site n → Mat) (r / 2),
      ‖fderiv ℂ (fun X => blockAvg (UX (N := N) X) lam' y h) X‖ ≤ 2 * K / r := fun X hX => by
    have hXb := hsub hX
    rw [mem_closedBall, dist_zero_right] at hX
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    have := SchwarzCauchy.cauchy_fderiv hd (fun X' hX' => hK ((X', lam') : (Fin 4 → Site n → Mat) × (Site n → Mat))
      ⟨by rw [mem_ball, dist_zero_right] at hX'; rw [mem_closedBall, dist_zero_right]; exact hX'.le,
        by rw [mem_closedBall, dist_zero_right, hl'n]⟩) hXb v
    rw [sub_zero] at this
    calc _ ≤ K * ‖v‖ / (r - ‖X‖) := this
      _ ≤ 2 * K / r * ‖v‖ := by
          rw [div_le_iff₀ (by linarith)]
          have e : 2 * K / r * ‖v‖ * (r - ‖X‖) = K * ‖v‖ * (2 * (r - ‖X‖) / r) := by field_simp
          rw [e]
          have : 1 ≤ 2 * (r - ‖X‖) / r := by rw [le_div_iff₀ hr]; linarith
          nlinarith [mul_nonneg hK0 (norm_nonneg v)]
  have hmv := (convex_closedBall (0 : Fin 4 → Site n → Mat) (r / 2)).norm_image_sub_le_of_norm_fderiv_le
    (fun X hX => (hd.differentiableAt (isOpen_ball.mem_nhds (hsub hX)))) hder
    (by rw [mem_closedBall, dist_zero_right]; exact h2) (by rw [mem_closedBall, dist_zero_right]; exact h1)
  rw [hlin X₁, hlin X₂, ← smul_sub, norm_smul, Complex.norm_real, Real.norm_of_nonneg hlp.le]
  calc ‖lam‖ * ‖blockAvg (UX (N := N) X₁) lam' y h - blockAvg (UX (N := N) X₂) lam' y h‖
      ≤ ‖lam‖ * (2 * K / r * ‖X₁ - X₂‖) := mul_le_mul_of_nonneg_left hmv hlp.le
    _ = 2 * K / r * ‖X₁ - X₂‖ * ‖lam‖ := by ring

/-- The `0`-form of the reference torus with the values of `λ` on the box. -/
def ref0 (h : ℕ) (lam : Site n → Mat) (y : Site n) : Site (4 * h + 2) → Mat :=
  fun z => lam (ofs y (rep (0 : Site (4 * h + 2)) h z))

lemma norm_ref0_le (h : ℕ) (lam : Site n → Mat) (y : Site n) : ‖ref0 h lam y‖ ≤ ‖lam‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun z => norm_le_pi_norm lam _

/-- `Q'(𝐔_X)` at `y` is `Q'` of the reference torus at the box data. -/
lemma blockAvg_reference (h : ℕ) (X : Fin 4 → Site n → Mat) (lam : Site n → Mat) (y : Site n) :
    blockAvg (UX (N := N) X) lam y h = blockAvg (UX (N := N) (refForm h X y)) (ref0 h lam y) 0 h := by
  have hA := agree_ref h (UX (N := N) X) 0 y
  rw [refConfig_UX] at hA
  have ht := fun x => (trans_agree hA (endOK_zero h) x).1
  simp only [ofs_zero] at ht
  have hl : ∀ x : Pts h, ref0 h lam y (ofs 0 (offP h x)) = lam (ofs y (offP h x)) := fun x => by
    simp only [ref0]
    rw [rep_ofs 0 h fun σ => by have := offP_inM h x σ; push_cast; constructor <;> omega]
  simp only [blockAvg, ht, hl]

/-- **`Q'(𝐔_X)` is Lipschitz in `X`, uniformly**: `‖(Q'(𝐔_{X₁}) - Q'(𝐔_{X₂}))λ‖ ≤ C‖X₁ - X₂‖‖λ‖` on every torus. -/
theorem uniform_blockAvg_lip (h : ℕ) (μ : Fin 4) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ∀ {n : ℕ} [NeZero n] (y : Site n) (lam : Site n → Mat)
      (X₁ X₂ : Fin 4 → Site n → Mat), ‖X₁‖ ≤ r → ‖X₂‖ ≤ r →
      ‖blockAvg (UX (N := N) X₁) lam y h - blockAvg (UX (N := N) X₂) lam y h‖ ≤ C * ‖X₁ - X₂‖ * ‖lam‖ := by
  obtain ⟨r, K, hr, -, hc, -⟩ := bounds_UX (N := N) (n := 4 * h + 2) 0 μ h
  obtain ⟨C, hC, hlip⟩ := blockAvg_lip_UX (N := N) hr hc
  refine ⟨r / 2, C, by positivity, hC, fun {n} _ y lam X₁ X₂ h1 h2 => ?_⟩
  rw [blockAvg_reference h X₁ lam y, blockAvg_reference h X₂ lam y]
  refine (hlip _ _ _ ((norm_refForm_le h y X₁).trans h1) ((norm_refForm_le h y X₂).trans h2)).trans ?_
  have e : refForm h X₁ y - refForm h X₂ y = refForm h (X₁ - X₂) y := rfl
  rw [e]
  have h3 := mul_le_mul_of_nonneg_left (norm_refForm_le h y (X₁ - X₂)) hC
  exact mul_le_mul h3 (norm_ref0_le h lam y) (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))

/-- **`Q'(𝐔)λ = Q'(𝐔_X)Ad_uλ`** in the reduction. -/
theorem blockAvg_reduce {U : Config N n} {h : ℕ} {y : Site n} {μ : Fin 4} {A' X : Fin 4 → Site n → Mat}
    (hn : 4 * h + 4 ≤ n)
    (hag : ∀ ρ z, BoxBond y h μ ρ z → ((moveC U A').gauge (uG U y h)) ρ z = UX X ρ z)
    (hU : U.IsGaugeField) (hg : GoodAt (UX (N := N) X) y h) (lam : Site n → Mat) :
    blockAvg (moveC U A') lam y h = blockAvg (UX (N := N) X) (fun z => Ad (uG U y h z) (lam z)) y h := by
  set u := uG U y h
  set W := (moveC U A').gauge u
  have hn2 : 4 * h + 2 ≤ n := by omega
  have hu : ∀ z, ((u z : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ := fun z => hol_unitary' U hU _
  have hm : ∀ ρ z, Bm y h z → Bm y h (z + unit n ρ) → W ρ z = UX X ρ z := fun ρ z h1 h2 =>
    hag ρ z ⟨Or.inl h1, Or.inl h2⟩
  have hY : ∀ x i, ‖expsG W y h x i‖ ≤ 1 / 1024 := fun x i => by
    rw [expsG_local hn2 hm x]; exact hg.expsG_le x i
  have hw : ∀ Z : Mat, ‖Ad ((fun z => (u z)⁻¹) y) Z‖ ≤ 2 * ‖Z‖ := fun Z => by
    rw [SupportCont.opNorm_Ad_unitary (SupportCont.unitary_inv (hu _))]; linarith [norm_nonneg Z]
  have hb := blockAvg_gauge W (fun z => (u z)⁻¹) (fun z => Ad (u z) (lam z)) y h hw hY
  rw [gauge_gauge_inv] at hb
  have e : (fun z => Ad (u z)⁻¹ (Ad (u z) (lam z))) = lam := by
    funext z; rw [← Ad_mul', inv_mul_cancel, Ad_one]
  simp only [e] at hb
  rw [hb]
  have hw0 : (u y)⁻¹ = 1 := by simp only [u, uG_base U hn y, _root_.inv_one]
  simp only [hw0, Ad_one]
  simp only [blockAvg, trans_local hn2 hm]

/-- **(vii) for `Q'`**: `‖(Q'(e^{iaA'₁}U) - Q'(e^{iaA'₂}U))λ‖ ≤ C₁‖a(A'₁ - A'₂)‖_{∞,box}‖λ‖_∞`, with `c, C₁`
depending on `L` and `G` only. -/
theorem relative_average_vii_Q' (h : ℕ) (μ : Fin 4) :
    ∃ c C₁ : ℝ, 0 < c ∧ 0 ≤ C₁ ∧
      ∀ {n : ℕ} [NeZero n] (U : Config N n), U.IsGaugeField → 4 * h + 4 ≤ n → ∀ (y : Site n)
        [DecidablePred (InBoxB y h μ)] (α₀ α₁ : ℝ), 0 ≤ α₀ → 0 ≤ α₁ → α₀ ≤ c → α₁ ≤ c →
        (∀ μ' ν' z, PlaqIn (boxR y (loD h) (hiD h μ μ)) μ' ν' z →
          hs (((plaq U μ' ν' z : GLN) : Mat) - 1) ≤ α₀) →
        ∀ A'₁ A'₂ : Fin 4 → Site n → Mat, (∀ ρ z, BoxBond y h μ ρ z → ‖A'₁ ρ z‖ ≤ α₁) →
        (∀ ρ z, BoxBond y h μ ρ z → ‖A'₂ ρ z‖ ≤ α₁) → ∀ lam : Site n → Mat,
          ‖blockAvg (moveC U A'₁) lam y h - blockAvg (moveC U A'₂) lam y h‖ ≤
            C₁ * ‖restrictF (A'₁ - A'₂) (InBoxB y h μ)‖ * ‖lam‖ := by
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
  refine ⟨c, 24 * C, by positivity, by positivity, ?_⟩
  intro n _ U hU hn y _ α₀ α₁ hα₀ hα₁ hα₀c hα₁c hplq A'₁ A'₂ hA₁ hA₂ lam
  obtain ⟨X₁, hX1c, -, hag₁, hl₁, hz₁⟩ := reduce_box_supp hU hn y μ hα₀ hα₁ hα₀c hα₁c hc2 hplq A'₁ hA₁
  obtain ⟨X₂, hX2c, -, hag₂, hl₂, hz₂⟩ := reduce_box_supp hU hn y μ hα₀ hα₁ hα₀c hα₁c hc2 hplq A'₂ hA₂
  have hKc : K * c ≤ m / 2 := by
    calc K * c ≤ K * (m / (2 * K)) := mul_le_mul_of_nonneg_left hc1 hKpos.le
      _ = m / 2 := by field_simp
  have hK8 : K * c ≤ 1 / 8 := by
    calc K * c ≤ K * (1 / (8 * K)) := mul_le_mul_of_nonneg_left hc2 hKpos.le
      _ = 1 / 8 := by field_simp
  have hmci : m ≤ ci := min_le_left _ _
  have hmr : m ≤ r := min_le_right _ _
  have hu : ∀ z, ((uG U y h z : GLN) : Mat) ∈ unitaryGroup (Fin N) ℂ := fun z => hol_unitary' U hU _
  have hc8 : c ≤ 1 / 8 := hc2.trans (by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith)
  have hg₁ := (hpol y X₁ 0 (by linarith) (by rw [norm_zero]; exact hci)).g0
  have hg₂ := (hpol y X₂ 0 (by linarith) (by rw [norm_zero]; exact hci)).g0
  rw [blockAvg_reduce hn hag₁ hU hg₁, blockAvg_reduce hn hag₂ hU hg₂]
  refine (hlip y _ X₁ X₂ (by linarith) (by linarith)).trans ?_
  have hlam : ‖(fun z => Ad (uG U y h z) (lam z))‖ = ‖lam‖ := by
    apply le_antisymm
    · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun z => by
        rw [SupportCont.opNorm_Ad_unitary (hu z)]; exact norm_le_pi_norm lam z
    · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun z => by
        have := norm_le_pi_norm (fun z => Ad (uG U y h z) (lam z)) z
        rwa [SupportCont.opNorm_Ad_unitary (hu z)] at this
  rw [hlam]
  have hXl := X_lip hU y μ (fun ρ z hb => (hA₁ ρ z hb).trans (hα₁c.trans hc8))
    (fun ρ z hb => (hA₂ ρ z hb).trans (hα₁c.trans hc8)) (by linarith) (by linarith) hag₁ hag₂ hl₁ hl₂ hz₁ hz₂
  have h1 : C * ‖X₁ - X₂‖ ≤ C * (24 * ‖restrictF (A'₁ - A'₂) (InBoxB y h μ)‖) := mul_le_mul_of_nonneg_left hXl hC
  calc C * ‖X₁ - X₂‖ * ‖lam‖ ≤ C * (24 * ‖restrictF (A'₁ - A'₂) (InBoxB y h μ)‖) * ‖lam‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = 24 * C * ‖restrictF (A'₁ - A'₂) (InBoxB y h μ)‖ * ‖lam‖ := by ring

end RelativeAverage
end CoreLean

end
