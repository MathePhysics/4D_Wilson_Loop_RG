/-
`lem:average`(vi) of BALABAN_CORE.tex (`c150c9917e21`), the consistency (i) for complex `B`, on the lattice:
`M(𝐔_B)(c⁻¹) = M(𝐔_B)(c)⁻¹` for `𝐔_B = e^{iB}U`, `‖B‖_∞ < r_M`.

The core derives this from the identity theorem (both sides are holomorphic in `B` and agree for `B` with
values in `𝔤`). Here it is proved directly, for every `B` in the ball, from two properties of the series
`Log`: `Log(gWg⁻¹) = Ad_g Log W` for every invertible `g` (`LogM_conj`), and `Log W⁻¹ = -Log W` for
`‖W - 1‖ ≤ ¼` (`LogM_inv`). The loops of `c⁻¹` are `𝐔_B([c])⁻¹𝐔_B(ℓ_c)⁻¹𝐔_B([c])`, so
`β_{c⁻¹} = -Ad_{𝐔_B([c])⁻¹}β_c` and `M(𝐔_B)(c⁻¹) = 𝐔_B([c])⁻¹e^{-iβ_c} = M(𝐔_B)(c)⁻¹`.

* `lpathRev`, `betaLogRev`, `avgLogURev`: the loops `ℓ_{c⁻¹}(x, Γ', Γ) = Γ' · [x', x] · Γ⁻¹ · [c]`, the exponent
  and the average of the reversed bond `c⁻¹ = (c₊, c₋)`, with the series `Log`.
* `avgLogURev_eq`: `M(V)(c⁻¹) = M(V)(c)⁻¹` for every configuration `V` whose loops of `c` are within `¼` of `id`.
* `near_moveC`: `‖𝐔_B(γ) - 1‖ ≤ 2|γ|‖B‖_∞ + ‖U(γ) - 1‖`.
* `average_reverse_analytic`: for `U` and `B` as in `average_analytic`, the loops of `c⁻¹` of `𝐔_B` are within
  `¼` of `id` and `M(𝐔_B)(c⁻¹) = M(𝐔_B)(c)⁻¹`.
-/
import CoreLean.AverageHolo

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean

namespace AverageHolo

open LatticePaths LatticeKappa RegularAverages

set_option linter.unusedSectionVars false

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-- `Log W⁻¹ = -Log W` for `‖W - 1‖ ≤ ¼`: `‖Log W‖ ≤ ½ < log 2` and `W⁻¹ = e^{-Log W}`. -/
lemma LogM_inv {W : GLN} (hW : ‖(W : Mat) - 1‖ ≤ 1 / 4) :
    LogM ((W⁻¹ : GLN) : Mat) = -LogM (W : Mat) := by
  have hl2 := Real.log_two_gt_d9
  have hn : ‖LogM (W : Mat)‖ ≤ 1 / 2 :=
    (norm_LogM_le (hW.trans (by norm_num))).trans (by linarith)
  have hE : exp (LogM (W : Mat)) = (W : Mat) := exp_LogM (hW.trans_lt (by norm_num))
  have hWe : W = expU (LogM (W : Mat)) := Units.ext (by rw [expU_val, hE])
  have hWi : ((W⁻¹ : GLN) : Mat) = exp (-LogM (W : Mat)) := by
    conv_lhs => rw [hWe]
    rw [expU_inv, expU_val]
  rw [hWi, LogM_exp (by rw [norm_neg]; linarith)]

variable {n : ℕ} [NeZero n]

/-- `‖𝐔_B(γ) - 1‖ ≤ 2T + ‖U(γ) - 1‖` when `|γ|‖B‖_∞ ≤ T ≤ 1`. -/
lemma near_moveC {G : GaugeGroup N} {U : Config N n} (hU : IsGField G U) (B : Fin 4 → Site n → Mat)
    (γ : List (Bond n)) {T : ℝ} (hT : (γ.length : ℝ) * ‖B‖ ≤ T) (hT1 : T ≤ 1) :
    ‖(((moveC U B).hol γ : GLN) : Mat) - 1‖ ≤ 2 * T + ‖((U.hol γ : GLN) : Mat) - 1‖ := by
  obtain ⟨l, hl, hln, -, he⟩ := hol_decomp hU B γ
  have hT' : ((l.map fun Y => Complex.I • Y).map norm).sum ≤ T := by
    have := List.sum_le_length_nsmul ((l.map fun Y => Complex.I • Y).map norm) ‖B‖
      (by simpa [norm_I_smul'] using hln)
    simp only [List.length_map, nsmul_eq_mul] at this
    rw [hl] at this
    linarith
  have hE := (prod_exp_small (l.map fun Y => Complex.I • Y) hT' hT1).2
  have hEv : (((l.map fun Y => expU (Complex.I • Y)).prod : GLN) : Mat) =
      ((l.map fun Y => Complex.I • Y).map exp).prod := by
    rw [MeanTransports.val_prod_expU]; simp [List.map_map, Function.comp_def]
  rw [← hEv] at hE
  rw [he]
  have hUu : ((U.hol γ : GLN) : Mat) ∈ Matrix.unitaryGroup (Fin N) ℂ := hol_isU hU.gauge _
  rw [Units.val_mul]
  have e : (((l.map fun Y => expU (Complex.I • Y)).prod : GLN) : Mat) * ((U.hol γ : GLN) : Mat) - 1 =
      ((((l.map fun Y => expU (Complex.I • Y)).prod : GLN) : Mat) - 1) * ((U.hol γ : GLN) : Mat) +
        (((U.hol γ : GLN) : Mat) - 1) := by noncomm_ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [CStarRing.norm_mul_mem_unitary _ hUu]
  linarith

variable {ι : Type*} [Fintype ι] {P : ι → Type*} [∀ x, Fintype (P x)]

/-- The loop `ℓ_{c⁻¹}(x, Γ', Γ) = Γ' · [x', x] · Γ⁻¹ · [c]` of the reversed bond `c⁻¹ = (c₊, c₋)`, as a path:
for `c⁻¹` the paths of the two blocks are exchanged, `[x', x] = [x, x']⁻¹`, and `[c⁻¹]⁻¹ = [c]`. -/
def lpathRev (y : Site n) (κ : Fin 4) (L : ℕ) (off : ι → Fin 4 → ℤ) (ord : ∀ x, P x → List (Fin 4))
    (x : ι) (Γ' Γ : P x) : List (Bond n) :=
  stair (ofs y (Pi.single κ (L : ℤ))) (off x) (ord x Γ') 0 ++ rv (segZ κ (ofs y (off x)) L) ++
    rv (stair y (off x) (ord x Γ) 0) ++ segZ κ y L

/-- `β_{c⁻¹}` with the series `Log` (the weights of `c` and `c⁻¹` are the same). -/
def betaLogRev (V : Config N n) (y : Site n) (κ : Fin 4) (L : ℕ) (off : ι → Fin 4 → ℤ)
    (ord : ∀ x, P x → List (Fin 4)) : Mat :=
  ∑ x, ∑ Γ', ∑ Γ, Average.wt P P x • ((1 / Complex.I : ℂ) •
    LogM ((V.hol (lpathRev y κ L off ord x Γ' Γ) : GLN) : Mat))

/-- `M(V)(c⁻¹) = e^{iβ_{c⁻¹}}V([c⁻¹])` with the series `Log`. -/
def avgLogURev (V : Config N n) (y : Site n) (κ : Fin 4) (L : ℕ) (off : ι → Fin 4 → ℤ)
    (ord : ∀ x, P x → List (Fin 4)) : GLN :=
  expU (Complex.I • betaLogRev V y κ L off ord) * V.hol (rv (segZ κ y L))

/-- The loops of `c⁻¹` are `V([c])⁻¹V(ℓ_c)⁻¹V([c])`. -/
lemma hol_lpathRev (V : Config N n) (y : Site n) (κ : Fin 4) (L : ℕ) (off : ι → Fin 4 → ℤ)
    (ord : ∀ x, P x → List (Fin 4)) (x : ι) (Γ' Γ : P x) :
    V.hol (lpathRev y κ L off ord x Γ' Γ) =
      (V.hol (segZ κ y L))⁻¹ * (V.hol (lpath y κ L off ord x Γ Γ'))⁻¹ * V.hol (segZ κ y L) := by
  simp only [lpathRev, lpath, hol_append, rv, Transports.hol_rev]
  group

/-- **`lem:average`(i)** for the extension with `Log`: `M(V)(c⁻¹) = M(V)(c)⁻¹` for every configuration `V`
whose loops of `c` are within `¼` of `id`. -/
theorem avgLogURev_eq (V : Config N n) (y : Site n) (κ : Fin 4) (L : ℕ) (off : ι → Fin 4 → ℤ)
    (ord : ∀ x, P x → List (Fin 4))
    (hV : ∀ x Γ Γ', ‖((V.hol (lpath y κ L off ord x Γ Γ') : GLN) : Mat) - 1‖ ≤ 1 / 4) :
    avgLogURev V y κ L off ord = (avgLogU V y κ L off ord)⁻¹ := by
  -- `β_{c⁻¹} = -Ad_{V([c])⁻¹}β_c`
  have hb : betaLogRev V y κ L off ord = -Ad (V.hol (segZ κ y L))⁻¹ (betaLog V y κ L off ord) := by
    unfold betaLogRev betaLog
    simp only [Ad_sum, Ad_smul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun Γ _ => Finset.sum_congr rfl fun Γ' _ => ?_
    have e : (((V.hol (segZ κ y L))⁻¹ * (V.hol (lpath y κ L off ord x Γ Γ'))⁻¹ *
        V.hol (segZ κ y L) : GLN) : Mat) = Ad (V.hol (segZ κ y L))⁻¹
          (((V.hol (lpath y κ L off ord x Γ Γ'))⁻¹ : GLN) : Mat) := by
      simp only [Ad, Units.val_mul, inv_inv]
    rw [hol_lpathRev, e, LogM_conj, LogM_inv (hV x Γ Γ'), Ad_neg, smul_neg, smul_neg]
  unfold avgLogURev avgLogU
  rw [hb, rv, Transports.hol_rev, smul_neg, ← Ad_smul, ← Ad_neg, ← expU_conj, ← expU_inv]
  group

/-- The loops of `c⁻¹` have at most `6L` bonds. -/
lemma length_lpathRev {h : ℕ} (y : Site n) (κ : Fin 4) (off : ι → Fin 4 → ℤ)
    (ord : ∀ x, P x → List (Fin 4)) (hoff : ∀ x, AxialReference.InM h (off x))
    (hord : ∀ x Γ, (ord x Γ).Perm [0, 1, 2, 3]) (x : ι) (Γ' Γ : P x) :
    (lpathRev y κ (2 * h + 1) off ord x Γ' Γ).length ≤ 6 * (2 * h + 1) := by
  have := length_lpath y κ off ord hoff hord x Γ Γ'
  simp only [lpathRev, lpath, List.length_append, length_rv] at this ⊢
  omega

set_option maxHeartbeats 1000000 in
/-- **`lem:average`(vi), the consistency (i)** on the lattice: there is `c₀ > 0` (depending on `G` only) such
that for a `G`-valued `U` whose loops of `c = (y, y + Le_μ)` are within `c₀` of `id` and every `B` with
`‖B‖_∞ < c₀/L`, the loops of `c⁻¹` of `𝐔_B = e^{iB}U` are within `¼` of `id` (the domain of the formula for
`c⁻¹`), and `M(𝐔_B)(c⁻¹) = M(𝐔_B)(c)⁻¹`. The number `c₀` may be taken to be that of `average_analytic` when
it is at most `1/64`. -/
theorem average_reverse_analytic (G : GaugeGroup N) (hG : IsClosed G.mats) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ {n : ℕ} [NeZero n] (U : Config N n), IsGField G U →
      ∀ (h : ℕ) (y : Site n) (μ : Fin 4) {ι : Type} [Fintype ι] {P : ι → Type} [∀ x, Fintype (P x)]
      (off : ι → Fin 4 → ℤ) (ord : ∀ x, P x → List (Fin 4)), (∀ x, AxialReference.InM h (off x)) →
      (∀ x Γ, (ord x Γ).Perm [0, 1, 2, 3]) →
      (∀ x Γ Γ', ‖((U.hol (lpath y μ (2 * h + 1) off ord x Γ Γ') : GLN) : Mat) - 1‖ ≤ c₀) →
      ∀ B : Fin 4 → Site n → Mat, ‖B‖ < c₀ / ((2 * h + 1 : ℕ) : ℝ) →
        (∀ x Γ' Γ, ‖(((moveC U B).hol (lpathRev y μ (2 * h + 1) off ord x Γ' Γ) : GLN) : Mat) - 1‖ ≤
          1 / 4) ∧
        avgLogURev (moveC U B) y μ (2 * h + 1) off ord =
          (avgLogU (moveC U B) y μ (2 * h + 1) off ord)⁻¹ := by
  obtain ⟨c₀, hc₀, H⟩ := average_analytic G hG
  refine ⟨min c₀ (1 / 64), lt_min hc₀ (by norm_num), ?_⟩
  intro n _ U hU h y μ ι _ P _ off ord hoff hord hloops B hB
  have hc1 : min c₀ (1 / 64) ≤ c₀ := min_le_left _ _
  have hc2 : min c₀ (1 / 64) ≤ 1 / 64 := min_le_right _ _
  have hL1 : (1 : ℝ) ≤ ((2 * h + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * h + 1)
  have hBL : ‖B‖ * ((2 * h + 1 : ℕ) : ℝ) ≤ min c₀ (1 / 64) := by
    rw [lt_div_iff₀ (by linarith)] at hB; linarith
  have hB' : ‖B‖ < c₀ / ((2 * h + 1 : ℕ) : ℝ) :=
    hB.trans_le (div_le_div_of_nonneg_right hc1 (by linarith))
  obtain ⟨hdom, -, -, -⟩ := H U hU h y μ off ord hoff hord fun x Γ Γ' => (hloops x Γ Γ').trans hc1
  refine ⟨fun x Γ' Γ => ?_, avgLogURev_eq _ _ _ _ _ _ (hdom B hB')⟩
  -- the loops of `c⁻¹` of `U` are unitary conjugates of the inverses of those of `c`
  have hk := hol_isU hU.gauge (segZ μ y ((2 * h + 1 : ℕ) : ℤ))
  have hW := hol_isU hU.gauge (lpath y μ (2 * h + 1) off ord x Γ Γ')
  have hUr : ‖((U.hol (lpathRev y μ (2 * h + 1) off ord x Γ' Γ) : GLN) : Mat) - 1‖ ≤ min c₀ (1 / 64) := by
    have hc : U.hol (lpathRev y μ (2 * h + 1) off ord x Γ' Γ) =
        (U.hol (segZ μ y ((2 * h + 1 : ℕ) : ℤ)))⁻¹ * (U.hol (lpath y μ (2 * h + 1) off ord x Γ Γ'))⁻¹ *
          (U.hol (segZ μ y ((2 * h + 1 : ℕ) : ℤ)))⁻¹⁻¹ := by
      rw [hol_lpathRev, inv_inv]
    rw [hc, norm_conj_sub_one' hk.inv, norm_inv_sub_one' hW]
    exact hloops x Γ Γ'
  have hlen : ((lpathRev y μ (2 * h + 1) off ord x Γ' Γ).length : ℝ) ≤ 6 * ((2 * h + 1 : ℕ) : ℝ) := by
    have := length_lpathRev y μ off ord hoff hord x Γ' Γ
    exact_mod_cast this
  have hT : ((lpathRev y μ (2 * h + 1) off ord x Γ' Γ).length : ℝ) * ‖B‖ ≤ 6 * min c₀ (1 / 64) := by
    calc ((lpathRev y μ (2 * h + 1) off ord x Γ' Γ).length : ℝ) * ‖B‖
        ≤ 6 * ((2 * h + 1 : ℕ) : ℝ) * ‖B‖ := mul_le_mul_of_nonneg_right hlen (norm_nonneg _)
      _ = 6 * (‖B‖ * ((2 * h + 1 : ℕ) : ℝ)) := by ring
      _ ≤ 6 * min c₀ (1 / 64) := by linarith
  have := near_moveC hU B (lpathRev y μ (2 * h + 1) off ord x Γ' Γ) hT (by linarith)
  linarith

end AverageHolo

end CoreLean

end
