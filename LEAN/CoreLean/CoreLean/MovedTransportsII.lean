/-
`lem:moved-transports`(ii) of BALABAN_CORE.tex (`a7d5e1f955b0`), in abstract form.

A path `Γ` of `𝐆(y, x)` has at most `2L` bonds, and moving the factors `e^{±iaA(b_k)}` to the left writes
`(e^{iaA}𝐔)(Γ) = E_Γ 𝐔(Γ)` with `E_Γ = Π_k e^{iY_k}`, `‖Y_k‖ ≤ 2‖aA‖_∞`; these combinatorial facts, and the
hypotheses of `lem:moved-transports` on the mean (holomorphy and the bound `2ϱ_G` of
`Y(X) = (1/i) Log 𝗆({e^{iX_Γ}})` from `lem:group-mean`, `𝗆({e^{iX_Γ}}) = id`), are the inputs.

* `exists_exp_prod`: `Π_k e^{iY_k} = e^{iZ}` with `‖Z‖ ≤ 2ms` for `m` factors of norm `≤ s`, `512ms ≤ 1`, by
  `lem:product` applied to the factors in turn (`Z ↦ Ψ(Y, Z)`, `eq:product-lipschitz` at `(0, Z)`, `(Y, Z)`).
* `moved_transports_ii`: `E_Γ = e^{iZ_Γ}` with `‖Z_Γ‖ ≤ 8L‖aA‖_∞` (the rule `ax`; the core has `16L‖aA‖_∞`),
  `E_Γe^{iX_Γ} = e^{iX'_Γ}` with `X'_Γ = Ψ(Z_Γ, X_Γ)`, `‖X'_Γ - X_Γ‖ ≤ 3‖Z_Γ‖ ≤ 24L‖aA‖_∞`, and
  `‖Y(X')‖ ≤ 16 · 24L‖aA‖_∞ ≤ 2^{11}L‖aA‖_∞` by `lem:moved-transports`(i) (the rule `m`), for
  `2^9L‖aA‖_∞ ≤ ϱ_G ≤ 1/32` and `‖X_Γ‖ ≤ ϱ_G/4`.
-/
import CoreLean.MovedTransports
import CoreLean.Psi

open NormedSpace Metric
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ

/-- `‖Ψ(Y, Z) - Y - Z‖ ≤ 256‖Z‖‖Y‖` for `‖Y‖, ‖Z‖ ≤ 1/32`: `eq:product-lipschitz` at `(0, Z)` and `(Y, Z)`. -/
lemma norm_psi_sub_add_le {Y Z : Mat} (hY : ‖Y‖ ≤ 1 / 32) (hZ : ‖Z‖ ≤ 1 / 32) :
    ‖psi Y Z - Y - Z‖ ≤ 256 * ‖Z‖ * ‖Y‖ := by
  have h := psi_lipschitz (X := 0) (Y := Z) (X' := Y) (Y' := Z) (by simp) hZ hY hZ
  rw [psi_zero_left (by linarith), sub_zero, sub_self, norm_zero, mul_zero, add_zero, sub_zero] at h
  have e : psi Y Z - Y - Z = psi Y Z - Z - Y := by abel
  rw [e, mul_assoc]
  exact h

/-- `Π_k e^{iY_k} = e^{iZ}` with `‖Z‖ ≤ 2ms` for `m` factors with `‖Y_k‖ ≤ s` and `512ms ≤ 1`. -/
theorem exists_exp_prod (l : List Mat) {s : ℝ} (hs : 0 ≤ s) (hl : ∀ Y ∈ l, ‖Y‖ ≤ s)
    (h512 : 512 * l.length * s ≤ 1) :
    ∃ Z : Mat, exp (Complex.I • Z) = (l.map fun Y => exp (Complex.I • Y)).prod ∧
      ‖Z‖ ≤ 2 * l.length * s := by
  induction l with
  | nil => exact ⟨0, by simp, by simp⟩
  | cons Y l ih =>
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at h512 ⊢
    have hk : (0 : ℝ) ≤ l.length := Nat.cast_nonneg _
    obtain ⟨Z, hZe, hZ⟩ := ih (fun Y' hY' => hl Y' (by simp [hY'])) (by nlinarith)
    have hY : ‖Y‖ ≤ s := hl Y (by simp)
    have hs512 : 512 * s ≤ 1 := by nlinarith
    have hY32 : ‖Y‖ ≤ 1 / 32 := by linarith
    have hZ32 : ‖Z‖ ≤ 1 / 32 := by nlinarith
    have hl2 := log_two_gt_eighth
    refine ⟨psi Y Z, ?_, ?_⟩
    · rw [exp_I_psi (by linarith), hZe, List.map_cons, List.prod_cons]
    · have h := norm_psi_sub_add_le hY32 hZ32
      have h1 : ‖psi Y Z‖ ≤ ‖Y‖ + ‖Z‖ + 256 * ‖Z‖ * ‖Y‖ := by
        have := norm_add₃_le (a := psi Y Z - Y - Z) (b := Y) (c := Z)
        rw [show psi Y Z - Y - Z + Y + Z = psi Y Z by abel] at this
        linarith
      have h2 : 256 * ‖Z‖ * ‖Y‖ ≤ 256 * (2 * l.length * s) * s :=
        mul_le_mul (mul_le_mul_of_nonneg_left hZ (by norm_num)) hY (norm_nonneg _) (by positivity)
      nlinarith

/-- The exponents of the proof of `lem:moved-transports`(ii): `E_Γ = e^{iZ_Γ}` with `‖Z_Γ‖ ≤ 8Lε`, and
`E_Γe^{iX_Γ} = e^{iX'_Γ}` with `X'_Γ = Ψ(Z_Γ, X_Γ)`, `‖X'_Γ - X_Γ‖ ≤ 24Lε`, `‖X'_Γ‖ ≤ ϱ/2`. -/
theorem moved_exponents {n : ℕ} {L ε ϱ : ℝ} (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (hϱ1 : ϱ ≤ 1 / 32) (hsmall : 2 ^ 9 * L * ε ≤ ϱ) (Ys : Fin n → List Mat)
    (hlen : ∀ Γ, ((Ys Γ).length : ℝ) ≤ 2 * L) (hY : ∀ Γ, ∀ Y ∈ Ys Γ, ‖Y‖ ≤ 2 * ε)
    (X : Fin n → Mat) (hX : ∀ Γ, ‖X Γ‖ ≤ ϱ / 4) :
    ∃ Z X' : Fin n → Mat,
      (∀ Γ, exp (Complex.I • Z Γ) = ((Ys Γ).map fun Y => exp (Complex.I • Y)).prod ∧
        ‖Z Γ‖ ≤ 8 * L * ε) ∧
      (∀ Γ, exp (Complex.I • X' Γ) = exp (Complex.I • Z Γ) * exp (Complex.I • X Γ) ∧
        ‖X' Γ - X Γ‖ ≤ 24 * L * ε ∧ ‖X' Γ‖ ≤ ϱ / 2) := by
  have hLε : 0 ≤ L * ε := mul_nonneg hL hε
  -- the exponent of `E_Γ`
  have hZex : ∀ Γ, ∃ Z : Mat, exp (Complex.I • Z) = ((Ys Γ).map fun Y => exp (Complex.I • Y)).prod ∧
      ‖Z‖ ≤ 8 * L * ε := fun Γ => by
    have hm := hlen Γ
    have hm0 : (0 : ℝ) ≤ (Ys Γ).length := Nat.cast_nonneg _
    obtain ⟨Z, hZe, hZ⟩ := exists_exp_prod (Ys Γ) (by linarith : (0 : ℝ) ≤ 2 * ε) (hY Γ) (by
      calc 512 * ((Ys Γ).length : ℝ) * (2 * ε) ≤ 512 * (2 * L) * (2 * ε) := by gcongr
        _ = 4 * (2 ^ 9 * L * ε) := by ring
        _ ≤ 1 := by linarith)
    refine ⟨Z, hZe, hZ.trans ?_⟩
    calc 2 * ((Ys Γ).length : ℝ) * (2 * ε) ≤ 2 * (2 * L) * (2 * ε) := by gcongr
      _ = 8 * L * ε := by ring
  choose Z hZe hZ using hZex
  set X' : Fin n → Mat := fun Γ => psi (Z Γ) (X Γ)
  have hZ32 : ∀ Γ, ‖Z Γ‖ ≤ 1 / 32 := fun Γ => by have := hZ Γ; nlinarith
  have hX128 : ∀ Γ, ‖X Γ‖ ≤ 1 / 128 := fun Γ => by have := hX Γ; linarith
  -- `‖X'_Γ - X_Γ‖ ≤ (1 + 256‖X_Γ‖)‖Z_Γ‖ ≤ 3‖Z_Γ‖`
  have hdiff : ∀ Γ, ‖X' Γ - X Γ‖ ≤ 24 * L * ε := fun Γ => by
    have h := norm_psi_sub_add_le (hZ32 Γ) (by linarith [hX128 Γ] : ‖X Γ‖ ≤ 1 / 32)
    have e : X' Γ - X Γ = (psi (Z Γ) (X Γ) - Z Γ - X Γ) + Z Γ := by simp only [X']; abel
    have h3 : ‖X' Γ - X Γ‖ ≤ 3 * ‖Z Γ‖ := by
      rw [e]
      refine (norm_add_le _ _).trans ?_
      have : 256 * ‖X Γ‖ * ‖Z Γ‖ ≤ 2 * ‖Z Γ‖ := by
        have := hX128 Γ
        nlinarith [norm_nonneg (Z Γ)]
      linarith
    have := hZ Γ
    linarith
  have hX'n : ∀ Γ, ‖X' Γ‖ ≤ ϱ / 2 := fun Γ => by
    have h1 := norm_sub_norm_le (X' Γ) (X Γ)
    have := hdiff Γ; have := hX Γ
    nlinarith
  refine ⟨Z, X', fun Γ => ⟨hZe Γ, hZ Γ⟩, fun Γ => ⟨?_, hdiff Γ, hX'n Γ⟩⟩
  have hl2 := log_two_gt_eighth
  exact exp_I_psi (by linarith [hZ32 Γ, hX128 Γ])

/-- `lem:moved-transports`(ii). For paths `Γ` (an index type `Fin n`): the factors `Ys Γ` of `E_Γ`, at most
`2L` of them, with norms `≤ 2ε`, `ε = ‖aA‖_∞`; the exponents `X_Γ` of `𝐔(Γ)𝐔_m(y, x)⁻¹ = e^{iX_Γ}`, with
`‖X_Γ‖ ≤ ϱ/4`; the function `Y = (1/i) Log 𝗆` holomorphic on the polydisc of radius `ϱ`, bounded by `2ϱ`,
with `Y(X) = 0`. Then `E_Γ = e^{iZ_Γ}`, `E_Γe^{iX_Γ} = e^{iX'_Γ}`, and `‖Y(X')‖ ≤ 2^{11}Lε`. (For the actual
mean, without the holomorphy, see `MeanTransports.moved_transports_ii_mean`.) -/
theorem moved_transports_ii {n : ℕ} {L ε ϱ : ℝ} (hL : 0 ≤ L) (hε : 0 ≤ ε) (hϱ : 0 < ϱ)
    (hϱ1 : ϱ ≤ 1 / 32) (hsmall : 2 ^ 9 * L * ε ≤ ϱ) (Ys : Fin n → List Mat)
    (hlen : ∀ Γ, ((Ys Γ).length : ℝ) ≤ 2 * L) (hY : ∀ Γ, ∀ Y ∈ Ys Γ, ‖Y‖ ≤ 2 * ε)
    (X : Fin n → Mat) (hX : ∀ Γ, ‖X Γ‖ ≤ ϱ / 4) {Ym : (Fin n → Mat) → Mat}
    (hYm : DifferentiableOn ℂ Ym (ball 0 ϱ)) (hYmb : ∀ W ∈ ball (0 : Fin n → Mat) ϱ, ‖Ym W‖ ≤ 2 * ϱ)
    (hm0 : Ym X = 0) :
    ∃ Z X' : Fin n → Mat,
      (∀ Γ, exp (Complex.I • Z Γ) = ((Ys Γ).map fun Y => exp (Complex.I • Y)).prod ∧
        ‖Z Γ‖ ≤ 8 * L * ε) ∧
      (∀ Γ, exp (Complex.I • X' Γ) = exp (Complex.I • Z Γ) * exp (Complex.I • X Γ) ∧
        ‖X' Γ - X Γ‖ ≤ 24 * L * ε ∧ ‖X' Γ‖ ≤ ϱ / 2) ∧
      ‖Ym X'‖ ≤ 2 ^ 11 * L * ε := by
  obtain ⟨Z, X', hZ, hX'⟩ := moved_exponents hL hε hϱ1 hsmall Ys hlen hY X hX
  refine ⟨Z, X', hZ, hX', ?_⟩
  have hLε : 0 ≤ L * ε := mul_nonneg hL hε
  have h := moved_transports_i hϱ hYm hYmb (fun Γ => by linarith [hX Γ]) (fun Γ => (hX' Γ).2.2)
    (by positivity : (0 : ℝ) ≤ 24 * L * ε) (fun Γ => (hX' Γ).2.1)
  rw [hm0, sub_zero] at h
  nlinarith

end CoreLean

end
