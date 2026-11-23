/-
`lem:average`(v) of BALABAN_CORE.tex (`f1da63a7f109`), the domain of the average, on the lattice.

If `|U(∂p) - id| ≤ α` for the plaquettes with corners in `B(c₋) ∪ B(c₊)` and `αL²` is small, then every loop
of `c` lies in the domain of the chart with `‖U(ℓ) - id‖ ≤ 96√NL²α ≤ r_G`, so that `U ∈ 𝒪_c`, and
`‖β_c(U)‖ ≤ 192√NL²α` (the core's `C_M = 7√NL²`; the numbers are fixed here by the axial gauge).
* `loops_domain`: for a field with `V(b) = e^{iA_b}`, `‖A_b‖ ≤ a` on the bonds of the paths, the loops are
  within `2s` of `id`, in the chart, and `‖β_c‖ ≤ 4s`, `s = m₀a`.
* `average_domain`: the gauge `u(z) = U(τ_z)` from `c₋` on the box `B(c₋) ∪ B(c₊)` (the box `Δ` with
  `ν = μ`), in which the bonds are close to `id` (`gauge_bound`); the loops, based at `c₋` where `u = id`, are
  those of `U^u`.
-/
import CoreLean.RegularAverages

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean

namespace RegularAverages

open LatticePaths LatticeKappa

set_option linter.unusedSectionVars false

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

variable {G : GaugeGroup N} {ι : Type*} [Fintype ι] {P : ι → Type*} [∀ x, Fintype (P x)]

/-- The loops and the exponent of a field with small logarithms on the bonds of the paths. -/
theorem loops_domain {r : ℝ} (hch : ChartR G r) {n : ℕ} [NeZero n] (V : Config N n)
    (hV : IsGField G V) (A : Bond n → Mat) (hrev : ∀ b, A b.rev = -A b) (a : ℝ) (m₀ : ℕ)
    (y : Site n) (κ : Fin 4) (L : ℕ) (off : ι → Fin 4 → ℤ) (ord : ∀ x, P x → List (Fin 4))
    (hι : 0 < Fintype.card ι) (hP : ∀ x, 0 < Fintype.card (P x))
    (hg : ∀ x Γ, ∀ b ∈ stair y (off x) (ord x Γ) 0, Good V A a b)
    (hg' : ∀ x Γ, ∀ b ∈ stair (ofs y (Pi.single κ (L : ℤ))) (off x) (ord x Γ) 0, Good V A a b)
    (hh : ∀ x, ∀ b ∈ segZ κ (ofs y (off x)) L, Good V A a b) (hk : ∀ b ∈ segZ κ y L, Good V A a b)
    (hlen : ∀ x Γ Γ', (stair y (off x) (ord x Γ) 0).length + (segZ κ (ofs y (off x)) L).length +
        (stair (ofs y (Pi.single κ (L : ℤ))) (off x) (ord x Γ') 0).length + (segZ κ y L).length ≤ m₀)
    (ha : 0 ≤ a) (hs : m₀ * a ≤ 1 / 4) (hsr : 2 * (m₀ * a) ≤ r) :
    (∀ x Γ Γ', G.inChart (Average.loop (fun x Γ => V.hol (stair y (off x) (ord x Γ) 0))
        (fun x => V.hol (segZ κ (ofs y (off x)) L))
        (fun x Γ' => V.hol (stair (ofs y (Pi.single κ (L : ℤ))) (off x) (ord x Γ') 0))
        (V.hol (segZ κ y L)) x Γ Γ') ∧
      ‖((Average.loop (fun x Γ => V.hol (stair y (off x) (ord x Γ) 0))
        (fun x => V.hol (segZ κ (ofs y (off x)) L))
        (fun x Γ' => V.hol (stair (ofs y (Pi.single κ (L : ℤ))) (off x) (ord x Γ') 0))
        (V.hol (segZ κ y L)) x Γ Γ' : GLN) : Mat) - 1‖ ≤ 2 * (m₀ * a)) ∧
    ‖Average.beta G.chartLog (fun x Γ => V.hol (stair y (off x) (ord x Γ) 0))
        (fun x => V.hol (segZ κ (ofs y (off x)) L))
        (fun x Γ' => V.hol (stair (ofs y (Pi.single κ (L : ℤ))) (off x) (ord x Γ') 0))
        (V.hol (segZ κ y L))‖ ≤ 4 * (m₀ * a) := by
  set s : ℝ := m₀ * a with hs_def
  have hs0 : 0 ≤ s := by positivity
  set gp : ∀ x, P x → List (Bond n) := fun x Γ => stair y (off x) (ord x Γ) 0 with hgp
  set gp' : ∀ x, P x → List (Bond n) :=
    fun x Γ => stair (ofs y (Pi.single κ (L : ℤ))) (off x) (ord x Γ) 0 with hgp'
  set hp : ι → List (Bond n) := fun x => segZ κ (ofs y (off x)) L with hhp
  set kp : List (Bond n) := segZ κ y L with hkp
  set lp : ∀ x, P x → P x → List (Bond n) := fun x Γ Γ' => gp x Γ ++ hp x ++ rv (gp' x Γ') ++ rv kp
    with hlp
  have hloop : ∀ x Γ Γ', Average.loop (fun x Γ => V.hol (gp x Γ)) (fun x => V.hol (hp x))
      (fun x Γ' => V.hol (gp' x Γ')) (V.hol kp) x Γ Γ' = V.hol (lp x Γ Γ') := fun x Γ Γ' => by
    simp only [Average.loop, hlp, hol_append, rv, Transports.hol_rev]
  have hgood : ∀ x Γ Γ', ∀ b ∈ lp x Γ Γ', Good V A a b := fun x Γ Γ' b hb => by
    simp only [hlp, List.mem_append] at hb
    rcases hb with ((hb | hb) | hb) | hb
    · exact hg x Γ b hb
    · exact hh x b hb
    · exact good_rv hrev (hg' x Γ') b hb
    · exact good_rv hrev hk b hb
  have hlenl : ∀ x Γ Γ', ((lp x Γ Γ').length : ℝ) * a ≤ s := fun x Γ Γ' => by
    have : (lp x Γ Γ').length ≤ m₀ := by
      simp only [hlp, List.length_append, length_rv]
      exact hlen x Γ Γ'
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast this) ha
  have hs1 : s ≤ 1 := by linarith
  have hnear : ∀ x Γ Γ', ‖((V.hol (lp x Γ Γ') : GLN) : Mat) - 1‖ ≤ 2 * s := fun x Γ Γ' => by
    have h := hol_lin V A (lp x Γ Γ') (fun b hb => (hgood x Γ Γ' b hb).1)
      (fun b hb => (hgood x Γ Γ' b hb).2) ((hlenl x Γ Γ').trans hs1)
    exact h.2.trans (by linarith [hlenl x Γ Γ'])
  have hchart : ∀ x Γ Γ', G.inChart (V.hol (lp x Γ Γ')) ∧
      G.chartLog (V.hol (lp x Γ Γ')) = LogM ((V.hol (lp x Γ Γ') : GLN) : Mat) := fun x Γ Γ' => by
    obtain ⟨A', hA', hn', he', hl', -⟩ := hch _ (hV.hol_mem _) ((hnear x Γ Γ').trans hsr)
    obtain ⟨hin, hlog⟩ := GaugeGroup.chartLog_eq hA' hn' he'.symm
    exact ⟨hin, hlog.trans hl'.symm⟩
  refine ⟨fun x Γ Γ' => ?_, ?_⟩
  · show G.inChart (Average.loop (fun x Γ => V.hol (gp x Γ)) (fun x => V.hol (hp x))
      (fun x Γ' => V.hol (gp' x Γ')) (V.hol kp) x Γ Γ') ∧ _
    rw [hloop]
    exact ⟨(hchart x Γ Γ').1, hnear x Γ Γ'⟩
  · show ‖Average.beta G.chartLog (fun x Γ => V.hol (gp x Γ)) (fun x => V.hol (hp x))
      (fun x Γ' => V.hol (gp' x Γ')) (V.hol kp)‖ ≤ 4 * s
    unfold Average.beta
    simp only [hloop]
    refine norm_wsum_le hι hP _ fun x Γ Γ' => ?_
    rw [(hchart x Γ Γ').2, norm_smul, show ‖(1 / Complex.I : ℂ)‖ = 1 by simp, one_mul]
    refine (norm_LogM_le ((hnear x Γ Γ').trans (by linarith))).trans ?_
    linarith [hnear x Γ Γ']

/-! ### The box `B(c₋) ∪ B(c₊)` -/

variable {n : ℕ} [NeZero n]

lemma inB_of_inM {h : ℕ} {μ : Fin 4} {v : Fin 4 → ℤ} (hv : AxialReference.InM h v) :
    LatticePaths.InBox (loD h) (hiD h μ μ) v := fun σ => by
  have := hv σ
  simp only [loD, hiD, or_self]
  split_ifs <;> omega

lemma inB_of_seg {h : ℕ} {μ : Fin 4} {v : Fin 4 → ℤ} (hv : AxialReference.InM h v) {i : ℕ}
    (hi : i ≤ 2 * h + 1) : LatticePaths.InBox (loD h) (hiD h μ μ) (v + Pi.single μ (i : ℤ)) := fun σ => by
  have := hv σ
  simp only [loD, hiD, or_self, Pi.add_apply, Pi.single_apply]
  split_ifs <;> omega

lemma inB_of_shift {h : ℕ} {μ : Fin 4} {v : Fin 4 → ℤ} (hv : AxialReference.InM h v) :
    LatticePaths.InBox (loD h) (hiD h μ μ) (Pi.single μ ((2 * h + 1 : ℕ) : ℤ) + v) := fun σ => by
  have := hv σ
  simp only [loD, hiD, or_self, Pi.add_apply, Pi.single_apply]
  split_ifs <;> push_cast <;> omega

/-- The hypotheses of `loops_domain` for the coarse bond `(y, y + Le_μ)`. -/
lemma bond_hyps_one {V : Config N n} {A : Bond n → Mat} {a : ℝ} {h : ℕ} {y : Site n} {μ : Fin 4}
    (gd : ∀ (t : Bond n) (v v' : Fin 4 → ℤ), LatticePaths.InBox (loD h) (hiD h μ μ) v →
      LatticePaths.InBox (loD h) (hiD h μ μ) v' → t.site = ofs y v → t.plus = ofs y v' → Good V A a t)
    (off : ι → Fin 4 → ℤ) (ord : ∀ x, P x → List (Fin 4))
    (hoff : ∀ x, AxialReference.InM h (off x)) (hord : ∀ x Γ, (ord x Γ).Perm [0, 1, 2, 3]) :
    (∀ x Γ, ∀ b ∈ stair y (off x) (ord x Γ) 0, Good V A a b) ∧
    (∀ x Γ, ∀ b ∈ stair (ofs y (Pi.single μ ((2 * h + 1 : ℕ) : ℤ))) (off x) (ord x Γ) 0, Good V A a b) ∧
    (∀ x, ∀ b ∈ segZ μ (ofs y (off x)) ((2 * h + 1 : ℕ) : ℤ), Good V A a b) ∧
    (∀ b ∈ segZ μ y ((2 * h + 1 : ℕ) : ℤ), Good V A a b) ∧
    (∀ x Γ Γ', (stair y (off x) (ord x Γ) 0).length +
      (segZ μ (ofs y (off x)) ((2 * h + 1 : ℕ) : ℤ)).length +
      (stair (ofs y (Pi.single μ ((2 * h + 1 : ℕ) : ℤ))) (off x) (ord x Γ') 0).length +
      (segZ μ y ((2 * h + 1 : ℕ) : ℤ)).length ≤ 6 * (2 * h + 1)) := by
  have hnd : ∀ x Γ, (ord x Γ).Nodup := fun x Γ => (hord x Γ).nodup_iff.2 (by decide)
  have hlen : ∀ x Γ (w : Site n), (stair w (off x) (ord x Γ) 0).length ≤ 4 * h := fun x Γ w => by
    rw [length_stair, ((hord x Γ).map _).sum_eq]
    have := hoff x
    have h0 := this 0; have h1 := this 1; have h2 := this 2; have h3 := this 3
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  refine ⟨fun x Γ b hb => ?_, fun x Γ b hb => ?_, fun x b hb => ?_, fun b hb => ?_, fun x Γ Γ' => ?_⟩
  · obtain ⟨v, v', hv, hv', hs, hp⟩ := stair_ends y y 0 (off x) (ofs_zero y).symm (hoff x) _ (hnd x Γ) b hb
    rw [zero_add] at hs hp
    exact gd b v v' (inB_of_inM hv) (inB_of_inM hv') hs hp
  · obtain ⟨v, v', hv, hv', hs, hp⟩ := stair_ends y _ _ (off x) rfl (hoff x) _ (hnd x Γ) b hb
    exact gd b _ _ (inB_of_shift hv) (inB_of_shift hv') hs hp
  · obtain ⟨i, hi, hs, hp⟩ := seg_ends y _ (off x) rfl μ (2 * h + 1) b hb
    exact gd b _ _ (inB_of_seg (hoff x) hi.le) (inB_of_seg (hoff x) hi) hs hp
  · obtain ⟨i, hi, hs, hp⟩ := seg_ends y y 0 (ofs_zero y).symm μ (2 * h + 1) b hb
    rw [zero_add] at hs hp
    have h0 : AxialReference.InM h 0 := fun σ => by simp
    exact gd b _ _ (by simpa using inB_of_seg (μ := μ) h0 hi.le) (by simpa using inB_of_seg (μ := μ) h0 hi)
      hs hp
  · have := hlen x Γ y
    have := hlen x Γ' (ofs y (Pi.single μ ((2 * h + 1 : ℕ) : ℤ)))
    simp only [length_segZ, Int.natAbs_natCast]
    omega

set_option maxHeartbeats 2000000 in
/-- **`lem:average`(v)** on the lattice: with `|U(∂p) - id| ≤ α` on the plaquettes with corners in
`B(c₋) ∪ B(c₊)` and `αL² ≤ c`, every loop of `c = (y, y + Le_μ)` lies in the domain of the chart, within
`96√NL²α` of `id`, and `‖β_c(U)‖ ≤ 192√NL²α`. -/
theorem average_domain (G : GaugeGroup N) (hG : IsClosed G.mats) (hN : 1 ≤ N) :
    ∃ c : ℝ, 0 < c ∧ ∀ {n : ℕ} [NeZero n] (U : Config N n), IsGField G U →
      ∀ (h : ℕ), 4 * h + 4 ≤ n → ∀ (y : Site n) (μ : Fin 4)
      {ι : Type} [Fintype ι] {P : ι → Type} [∀ x, Fintype (P x)] (off : ι → Fin 4 → ℤ)
      (ord : ∀ x, P x → List (Fin 4)), 0 < Fintype.card ι → (∀ x, 0 < Fintype.card (P x)) →
      (∀ x, AxialReference.InM h (off x)) → (∀ x Γ, (ord x Γ).Perm [0, 1, 2, 3]) →
      ∀ α : ℝ, 0 ≤ α → α * ((2 * h + 1 : ℕ) : ℝ) ^ 2 ≤ c →
      (∀ μ' ν' z, PlaqIn (boxR y (loD h) (hiD h μ μ)) μ' ν' z →
        hs (((plaq U μ' ν' z : GLN) : Mat) - 1) ≤ α) →
      (∀ x Γ Γ', G.inChart (Average.loop (fun x Γ => U.hol (stair y (off x) (ord x Γ) 0))
          (fun x => U.hol (segZ μ (ofs y (off x)) ((2 * h + 1 : ℕ) : ℤ)))
          (fun x Γ' => U.hol (stair (ofs y (Pi.single μ ((2 * h + 1 : ℕ) : ℤ))) (off x) (ord x Γ') 0))
          (U.hol (segZ μ y ((2 * h + 1 : ℕ) : ℤ))) x Γ Γ') ∧
        ‖((Average.loop (fun x Γ => U.hol (stair y (off x) (ord x Γ) 0))
          (fun x => U.hol (segZ μ (ofs y (off x)) ((2 * h + 1 : ℕ) : ℤ)))
          (fun x Γ' => U.hol (stair (ofs y (Pi.single μ ((2 * h + 1 : ℕ) : ℤ))) (off x) (ord x Γ') 0))
          (U.hol (segZ μ y ((2 * h + 1 : ℕ) : ℤ))) x Γ Γ' : GLN) : Mat) - 1‖ ≤
          96 * Real.sqrt N * ((2 * h + 1 : ℕ) : ℝ) ^ 2 * α) ∧
      ‖Average.beta G.chartLog (fun x Γ => U.hol (stair y (off x) (ord x Γ) 0))
          (fun x => U.hol (segZ μ (ofs y (off x)) ((2 * h + 1 : ℕ) : ℤ)))
          (fun x Γ' => U.hol (stair (ofs y (Pi.single μ ((2 * h + 1 : ℕ) : ℤ))) (off x) (ord x Γ') 0))
          (U.hol (segZ μ y ((2 * h + 1 : ℕ) : ℤ)))‖ ≤ 192 * Real.sqrt N * ((2 * h + 1 : ℕ) : ℝ) ^ 2 * α := by
  obtain ⟨r, hr0, hr1, hch⟩ := GaugeGroup.chart_ii (G := G) hG
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
  refine ⟨min r (1 / 2) / (2 ^ 14 * Real.sqrt N), by positivity, ?_⟩
  intro n _ U hU h hn y μ ι _ P _ off ord hι hP hoff hord α hα hαc hplq
  set L : ℕ := 2 * h + 1 with hL
  have hLr : (L : ℝ) = 2 * h + 1 := by rw [hL]; push_cast; ring
  have hL1 : (1 : ℝ) ≤ L := by rw [hLr]; have : (0 : ℝ) ≤ h := Nat.cast_nonneg h; linarith
  set q : ℝ := Real.sqrt N * α * (L : ℝ) ^ 2 with hq
  have hq0 : 0 ≤ q := by positivity
  have hqc : q ≤ min r (1 / 2) / 2 ^ 14 := by
    have := mul_le_mul_of_nonneg_left hαc hsN.le
    rw [hq, mul_assoc]
    calc Real.sqrt N * (α * (L : ℝ) ^ 2)
        ≤ Real.sqrt N * (min r (1 / 2) / (2 ^ 14 * Real.sqrt N)) := this
      _ = min r (1 / 2) / 2 ^ 14 := by field_simp
  have hqr : q ≤ r / 2 ^ 14 := hqc.trans (by have := min_le_left r (1 / 2); linarith)
  have hqh : q ≤ 1 / 2 ^ 15 := hqc.trans (by have := min_le_right r (1 / 2); linarith)
  set β : ℝ := Real.sqrt N * α with hβ
  have hβ0 : 0 ≤ β := by positivity
  have hPB : PlaqBound U (boxR y (loD h) (hiD h μ μ)) β := fun μ' ν' z _ hz =>
    (opNorm_le_sqrt_mul_hs _).trans (mul_le_mul_of_nonneg_left (hplq μ' ν' z hz) (Real.sqrt_nonneg _))
  set u := uG U y h with hu_def
  have hu : ∀ z, u z ∈ G.carrier := fun z => hU.hol_mem _
  set V := U.gauge u with hV_def
  have hVG : IsGField G V := fun ρ z =>
    G.carrier.mul_mem (G.carrier.mul_mem (hu z) (hU ρ z)) (G.carrier.inv_mem (hu _))
  set δ : ℝ := ((8 * h + 2 : ℕ) : ℝ) * β with hδ
  have h8 : ((8 * h + 2 : ℕ) : ℝ) ≤ 4 * L := by rw [hLr]; push_cast; linarith
  have hδL : δ ≤ 4 * L * β := mul_le_mul_of_nonneg_right h8 hβ0
  have hLL : (L : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
  have hLβ : (L : ℝ) * β ≤ q := by
    rw [hq, hβ]; nlinarith [mul_le_mul_of_nonneg_right hLL hβ0]
  have hδq : δ ≤ 4 * q := by
    calc δ ≤ 4 * L * β := hδL
      _ = 4 * (L * β) := by ring
      _ ≤ 4 * q := by linarith
  have hδ12 : δ ≤ 1 / 2 := by linarith
  have hVb : ∀ m ρ, LatticePaths.InBox (loD h) (hiD h μ μ) m →
      LatticePaths.InBox (loD h) (hiD h μ μ) (m + Pi.single ρ 1) →
      ‖((V ρ (ofs y m) : GLN) : Mat) - 1‖ ≤ δ := fun m ρ hm hm' =>
    gauge_bound U hU.gauge hn y μ μ hβ0 hPB m ρ hm hm'
  set a : ℝ := 2 * δ with ha
  have gd : ∀ (t : Bond n) (v v' : Fin 4 → ℤ), LatticePaths.InBox (loD h) (hiD h μ μ) v →
      LatticePaths.InBox (loD h) (hiD h μ μ) v' → t.site = ofs y v → t.plus = ofs y v' →
      Good V (Aof V) a t := fun t v v' hv hv' hs hp => good_of_ends V hn y μ μ hδ12 hVb t hv hv' hs hp
  have ha0 : 0 ≤ a := by positivity
  set s : ℝ := ((6 * L : ℕ) : ℝ) * a with hsdef
  have hsq : s ≤ 48 * q := by
    have e : s = 12 * L * δ := by rw [hsdef, ha]; push_cast; ring
    rw [e]
    calc 12 * (L : ℝ) * δ ≤ 12 * L * (4 * L * β) := mul_le_mul_of_nonneg_left hδL (by positivity)
      _ = 48 * q := by rw [hq, hβ]; ring
  obtain ⟨b1, b2, b3, b4, b5⟩ := bond_hyps_one gd off ord hoff hord
  have hD := loops_domain hch V hVG (Aof V) (Aof_rev V) a (6 * L) y μ L off ord hι hP b1 b2 b3 b4 b5 ha0
    (by linarith) (by linarith)
  -- the loops of `U` and of `V` agree, `u(y) = id`
  have hu0 : u y = 1 := by
    have hr0' : AxialReference.rep y h y = 0 := by
      have := AxialReference.rep_ofs y h (v := 0) (fun σ => by simp only [Pi.zero_apply]; omega)
      rwa [ofs_zero] at this
    rw [hu_def, uG, hr0']
    simp [stair, segZ_zero, Config.hol]
  have est : ∀ (w : Site n) x (Γ : P x), V.hol (stair w (off x) (ord x Γ) 0) =
      u w * U.hol (stair w (off x) (ord x Γ) 0) * (u (ofs w (off x)))⁻¹ := fun w x Γ => by
    have hc := chain_endpt_stair w (off x) (ord x Γ) 0
    rw [ofs_zero, zero_add, offs_perm _ (hord x Γ)] at hc
    rw [hV_def, hol_gauge U u _ w hc.1, hc.2]
  have eseg : ∀ (w : Site n), V.hol (segZ μ w (L : ℤ)) =
      u w * U.hol (segZ μ w (L : ℤ)) * (u (w + (L : ℤ) • unit n μ))⁻¹ := fun w => by
    rw [hV_def, hol_gauge U u _ w (chain_segZ μ w _), endpt_segZ]
  have e1 : ∀ x, ofs y (off x) + (L : ℤ) • unit n μ = ofs (ofs y (Pi.single μ (L : ℤ))) (off x) := fun x => by
    rw [ofs_ofs, add_comm (Pi.single μ _) (off x), ofs_add_single]
  have e2 : y + (L : ℤ) • unit n μ = ofs y (Pi.single μ (L : ℤ)) := by
    rw [← ofs_zero y, ← ofs_add_single, zero_add, ofs_zero]
  have hloopUV : ∀ x Γ Γ', Average.loop (fun x Γ => U.hol (stair y (off x) (ord x Γ) 0))
      (fun x => U.hol (segZ μ (ofs y (off x)) L))
      (fun x Γ' => U.hol (stair (ofs y (Pi.single μ (L : ℤ))) (off x) (ord x Γ') 0))
      (U.hol (segZ μ y L)) x Γ Γ' =
    Average.loop (fun x Γ => V.hol (stair y (off x) (ord x Γ) 0))
      (fun x => V.hol (segZ μ (ofs y (off x)) L))
      (fun x Γ' => V.hol (stair (ofs y (Pi.single μ (L : ℤ))) (off x) (ord x Γ') 0))
      (V.hol (segZ μ y L)) x Γ Γ' := fun x Γ Γ' => by
    simp only [Average.loop, est, eseg, e1, e2, hu0]
    group
  have hβUV : Average.beta G.chartLog (fun x Γ => U.hol (stair y (off x) (ord x Γ) 0))
      (fun x => U.hol (segZ μ (ofs y (off x)) L))
      (fun x Γ' => U.hol (stair (ofs y (Pi.single μ (L : ℤ))) (off x) (ord x Γ') 0))
      (U.hol (segZ μ y L)) =
    Average.beta G.chartLog (fun x Γ => V.hol (stair y (off x) (ord x Γ) 0))
      (fun x => V.hol (segZ μ (ofs y (off x)) L))
      (fun x Γ' => V.hol (stair (ofs y (Pi.single μ (L : ℤ))) (off x) (ord x Γ') 0))
      (V.hol (segZ μ y L)) := by
    unfold Average.beta
    simp only [hloopUV]
  have hc96 : 2 * s ≤ 96 * Real.sqrt N * (L : ℝ) ^ 2 * α := by
    have : 96 * Real.sqrt N * (L : ℝ) ^ 2 * α = 96 * q := by rw [hq]; ring
    rw [this]; linarith
  have hc192 : 4 * s ≤ 192 * Real.sqrt N * (L : ℝ) ^ 2 * α := by
    have : 192 * Real.sqrt N * (L : ℝ) ^ 2 * α = 192 * q := by rw [hq]; ring
    rw [this]; linarith
  refine ⟨fun x Γ Γ' => ?_, ?_⟩
  · rw [hloopUV]
    exact ⟨(hD.1 x Γ Γ').1, (hD.1 x Γ Γ').2.trans hc96⟩
  · rw [hβUV]
    exact hD.2.trans hc192

end RegularAverages

end CoreLean

end
