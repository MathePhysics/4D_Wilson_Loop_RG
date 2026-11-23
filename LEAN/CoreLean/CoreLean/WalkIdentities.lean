/-
The algebraic identities of the walk expansions of the block inverse and of `G` in BALABAN_CORE.tex
(`bf6b2bc552ba`), abstract form.

* `thm:walks`(i): `eq:first-remainder-block` (`first_remainder_block`) and `eq:first-remainder`
  (`first_remainder_G`), from the coincidence of the given and the local operators near a cube,
  which enters as hypotheses.
* `thm:walks`(ii): from a first remainder of norm less than one, the operator is invertible and its
  inverse is the series (`inverse_of_remainder`), for the block inverse and for `G` as for `G'`; and
  for symmetric operators `G = Σ_R^T G_0` (`inverse_transposed`).
* `lem:domain-difference`(ii): `G'F - G'_□F = -G' Z_□ G'_□ F` (`domain_difference`), and
  `G'^2 - G'^2_□ = G'(G' - G'_□) + (G' - G'_□)G'_□`, and the identity of
  `lem:scalar-block-inverse-walks` (`sq_domain_difference`).
* `lem:projection-difference`(ii): `χ₁ξ = Cν + Cρ`, `ρ = ρ₁ + ρ₂ + ρ₃`, and
  `χ (C_□ - C) ν = χ C ρ` (`block_inverse_difference`); (iii): the decomposition of `P - P_□`
  (`projection_difference`).

Operators are elements of a ring; the indicators are elements `χ`, and "the averages of the two
sequences coincide at the points of the cube, and their transposes on the functions supported there"
is `χ Q' = χ Q'_□` and `Q'^* χ = Q'^*_□ χ`. Not formalised here: the block bounds of the parts and the
convergence of the series in the block norms, which rest on `lem:domain-difference`(i), (iii),
`lem:composition`, and `lem:cube-small-field`(iii).
-/
import CoreLean.WalksG

open Finset

namespace CoreLean
namespace WalkIdentities

section Algebra

variable {R : Type*} [Ring R] {D : Type*} [Fintype D]

/-! ### The first remainder of `G` (`eq:first-remainder`) -/

/-- The factor `W_□ = K(h) + (DPD^* - DP_□D^*)h + P_{□,1}(h)` of `R_G`, with `K(h) = [h, A_s]`,
`P_{□,1}(h) = [DP_□D^*, h]`, `A_s = Δ(U) + DD^* + Q^*𝖺Q`, `Pp = DPD^*`, `Pq = DP_□D^*`. -/
def Wfac (A Pp Pq h : R) : R := (h * A - A * h) + (Pp - Pq) * h + (Pq * h - h * Pq)

/-- `[h, Δ_𝖺] = K(h) + P_1(h)` for `Δ_𝖺 = A_s - DPD^*`. -/
theorem comm_Delta (A Pp h : R) :
    h * (A - Pp) - (A - Pp) * h = (h * A - A * h) + (Pp * h - h * Pp) := by
  noncomm_ring

/-- `h(DPD^* - DP_□D^*) + P_1(h) = (DPD^* - DP_□D^*)h + P_{□,1}(h)`. -/
theorem comm_projections (Pp Pq h : R) :
    h * (Pp - Pq) + (Pp * h - h * Pp) = (Pp - Pq) * h + (Pq * h - h * Pq) := by
  noncomm_ring

/-- One cube of `eq:first-remainder`: `Δ_𝖺 F_□ = h_□² - V_□`, `F_□ = h_□G_□h_□`,
`V_□ = W_□G_□h_□`, from the locality `h_□ A_s G_□ h_□ = h_□ A_{s,□} G_□ h_□` and from
`h_□ (A_{s,□} - DP_□D^*) G_□ h_□ = h_□²`. -/
theorem first_remainder_cube (A Pp Aq Pq h G : R) (hloc : h * A * G * h = h * Aq * G * h)
    (hinv : h * (Aq - Pq) * G * h = h * h) :
    (A - Pp) * (h * G * h) = h * h - Wfac A Pp Pq h * G * h := by
  have e : h * h - Wfac A Pp Pq h * G * h =
      (A - Pp) * (h * G * h) - (h * (Aq - Pq) * G * h - h * h) - (h * A * G * h - h * Aq * G * h) := by
    unfold Wfac; noncomm_ring
  rw [e, hinv, hloc, sub_self, sub_self, sub_zero, sub_zero]

/-- `G_0 = Σ_□ h_□G_□h_□`. -/
def G0 (h G : D → R) : R := ∑ q, h q * G q * h q

/-- `R_G = Σ_□ W_□G_□h_□`. -/
def RG (A Pp : R) (Pq h G : D → R) : R := ∑ q, Wfac A Pp (Pq q) (h q) * G q * h q

/-- `thm:walks`(i), `eq:first-remainder`: `Δ_𝖺 G_0 = I - R_G`. -/
theorem first_remainder_G (A Pp : R) (Aq Pq h G : D → R)
    (hloc : ∀ q, h q * A * G q * h q = h q * Aq q * G q * h q)
    (hinv : ∀ q, h q * (Aq q - Pq q) * G q * h q = h q * h q) (hpart : ∑ q, h q * h q = 1) :
    (A - Pp) * G0 h G = 1 - RG A Pp Pq h G := by
  unfold G0 RG
  rw [Finset.mul_sum, ← hpart, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← mul_assoc, ← mul_assoc, mul_assoc (A - Pp), mul_assoc (A - Pp)]
  have := first_remainder_cube A Pp (Aq q) (Pq q) (h q) (G q) (hloc q) (hinv q)
  rw [← this]

/-! ### The first remainder of the block inverse (`eq:first-remainder-block`) -/

/-- The summand of `R_C`, without the sign:
`((1 - χ_□)Xh_□ + χ_□Q'(G'^2 - G'^2_□)Q'^*h_□ + [χ_□X_□, h_□])C_□h_□`. -/
def RCterm (X Q Qs G' χ h Gq Xq Cq : R) : R :=
  ((1 - χ) * X * h + χ * Q * (G' ^ 2 - Gq ^ 2) * Qs * h + (χ * Xq * h - h * (χ * Xq))) * Cq * h

/-- One cube of `eq:first-remainder-block`:
`Q'G'^2Q'^* h_□C_□h_□ = h_□² + RCterm`, from `X = Q'G'^2Q'^*`, `X_□ = Q'_□G'^2_□Q'^*_□`,
`χ_□Q' = χ_□Q'_□`, `Q'^*h_□ = Q'^*_□h_□`, `X_□C_□h_□ = h_□`, and `χ_□h_□ = h_□`. -/
theorem first_remainder_block_cube (Q Qs G' χ h Qq Qsq Gq Cq : R)
    (hQ : χ * Q = χ * Qq) (hQs : Qs * h = Qsq * h)
    (hX : Qq * Gq ^ 2 * Qsq * Cq * h = h) (hχ : χ * h = h) :
    Q * G' ^ 2 * Qs * (h * Cq * h) =
      h * h + RCterm (Q * G' ^ 2 * Qs) Q Qs G' χ h Gq (Qq * Gq ^ 2 * Qsq) Cq := by
  have e1 : χ * Q * Gq ^ 2 * Qs * h * Cq * h = χ * (Qq * Gq ^ 2 * Qsq) * h * Cq * h := by
    calc χ * Q * Gq ^ 2 * Qs * h * Cq * h = (χ * Q) * Gq ^ 2 * (Qs * h) * Cq * h := by noncomm_ring
      _ = (χ * Qq) * Gq ^ 2 * (Qsq * h) * Cq * h := by rw [hQ, hQs]
      _ = χ * (Qq * Gq ^ 2 * Qsq) * h * Cq * h := by noncomm_ring
  have e2 : h * (χ * (Qq * Gq ^ 2 * Qsq)) * Cq * h = h * h := by
    calc h * (χ * (Qq * Gq ^ 2 * Qsq)) * Cq * h = h * χ * (Qq * Gq ^ 2 * Qsq * Cq * h) := by
          noncomm_ring
      _ = h * (χ * h) := by rw [hX]; noncomm_ring
      _ = h * h := by rw [hχ]
  have e : h * h + RCterm (Q * G' ^ 2 * Qs) Q Qs G' χ h Gq (Qq * Gq ^ 2 * Qsq) Cq =
      Q * G' ^ 2 * Qs * (h * Cq * h) - (χ * Q * Gq ^ 2 * Qs * h * Cq * h -
        χ * (Qq * Gq ^ 2 * Qsq) * h * Cq * h) - (h * (χ * (Qq * Gq ^ 2 * Qsq)) * Cq * h - h * h) := by
    unfold RCterm; noncomm_ring
  rw [e, e1, e2, sub_self, sub_self, sub_zero, sub_zero]

/-- `thm:walks`(i), `eq:first-remainder-block`: `Q'G'^2Q'^*C_0 = I - R_C`, with
`C_0 = Σ_□ h_□C_□h_□` and `R_C = -Σ_□ RCterm`. -/
theorem first_remainder_block (Q Qs G' : R) (χ h Qq Qsq Gq Cq : D → R)
    (hQ : ∀ q, χ q * Q = χ q * Qq q) (hQs : ∀ q, Qs * h q = Qsq q * h q)
    (hX : ∀ q, Qq q * Gq q ^ 2 * Qsq q * Cq q * h q = h q) (hχ : ∀ q, χ q * h q = h q)
    (hpart : ∑ q, h q * h q = 1) :
    Q * G' ^ 2 * Qs * G0 h Cq =
      1 - -∑ q, RCterm (Q * G' ^ 2 * Qs) Q Qs G' (χ q) (h q) (Gq q) (Qq q * Gq q ^ 2 * Qsq q) (Cq q) := by
  rw [sub_neg_eq_add, ← hpart, ← Finset.sum_add_distrib]
  unfold G0
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← first_remainder_block_cube Q Qs G' (χ q) (h q) (Qq q) (Qsq q) (Gq q) (Cq q) (hQ q) (hQs q)
    (hX q) (hχ q)]

/-! ### `lem:domain-difference`(ii) -/

/-- `lem:domain-difference`(ii): if `G'Δ'_𝖺 = 1` and `Δ'_𝖺 G'_□F = F + Z_□G'_□F`, then
`G'F - G'_□F = -G'Z_□G'_□F`. -/
theorem domain_difference (G' Δ' Gq Z F : R) (hG : G' * Δ' = 1)
    (hZ : Δ' * (Gq * F) = F + Z * (Gq * F)) : G' * F - Gq * F = -(G' * Z * (Gq * F)) := by
  have : Gq * F = G' * F + G' * Z * (Gq * F) := by
    calc Gq * F = G' * Δ' * (Gq * F) := by rw [hG, one_mul]
      _ = G' * (Δ' * (Gq * F)) := by rw [mul_assoc]
      _ = G' * F + G' * Z * (Gq * F) := by rw [hZ, mul_add, mul_assoc]
  conv_lhs => rw [this]
  abel

/-- `G'^2 - G'^2_□ = G'(G' - G'_□) + (G' - G'_□)G'_□`. -/
theorem sq_difference (G' Gq : R) : G' ^ 2 - Gq ^ 2 = G' * (G' - Gq) + (G' - Gq) * Gq := by
  noncomm_ring

/-- The identity of the proof of `lem:scalar-block-inverse-walks`: `lem:domain-difference`(ii),
applied to `F` and to `G'_□F`, gives `(G'^2 - G'^2_□)F = -G'G'Z_□G'_□F - G'Z_□G'^2_□F`. -/
theorem sq_domain_difference (G' Δ' Gq Z F : R) (hG : G' * Δ' = 1)
    (hZ₁ : Δ' * (Gq * F) = F + Z * (Gq * F))
    (hZ₂ : Δ' * (Gq * (Gq * F)) = Gq * F + Z * (Gq * (Gq * F))) :
    (G' ^ 2 - Gq ^ 2) * F = -(G' * G' * Z * (Gq * F)) - G' * Z * (Gq ^ 2 * F) := by
  have h1 := domain_difference G' Δ' Gq Z F hG hZ₁
  have h2 := domain_difference G' Δ' Gq Z (Gq * F) hG hZ₂
  have e : (G' ^ 2 - Gq ^ 2) * F =
      G' * (G' * F - Gq * F) + (G' * (Gq * F) - Gq * (Gq * F)) := by
    noncomm_ring
  rw [e, h1, h2]
  noncomm_ring

/-! ### `lem:projection-difference` -/

/-- `lem:projection-difference`(ii): with `ξ = C_□ν`, `ρ = Xχ₁ξ - ν`, `CX = 1`,
`X = Q'G'^2Q'^*`, `X_□ = Q'_□G'^2_□Q'^*_□`, `X_□ξ = ν`, `χ₁ν = ν`, `χ₁Q' = χ₁Q'_□`,
`Q'^*χ₁ = Q'^*_□χ₁`, and an indicator `χ` of the points of the cube with `χχ₁ = χ`:
`χ₁ξ = Cν + Cρ`, `ρ = ρ₁ + ρ₂ + ρ₃`, and `χ(C_□ - C)ν = χCρ`. -/
theorem block_inverse_difference (Q Qs G' Qq Qsq Gq C Cq χ₁ χ ν : R)
    (hC : C * (Q * G' ^ 2 * Qs) = 1) (hXq : Qq * Gq ^ 2 * Qsq * (Cq * ν) = ν)
    (hν : χ₁ * ν = ν) (hQ : χ₁ * Q = χ₁ * Qq) (hQs : Qs * χ₁ = Qsq * χ₁) (hχ : χ * χ₁ = χ) :
    let X := Q * G' ^ 2 * Qs
    let Xq := Qq * Gq ^ 2 * Qsq
    let ξ := Cq * ν
    let ρ := X * (χ₁ * ξ) - ν
    χ₁ * ξ = C * ν + C * ρ ∧
      ρ = -(χ₁ * Xq * ((1 - χ₁) * ξ)) + χ₁ * Q * (G' ^ 2 - Gq ^ 2) * Qs * (χ₁ * ξ) +
        (1 - χ₁) * X * (χ₁ * ξ) ∧
      χ * (Cq * ν - C * ν) = χ * (C * ρ) := by
  intro X Xq ξ ρ
  have h1 : χ₁ * ξ = C * ν + C * ρ := by
    have : C * ν + C * ρ = C * X * (χ₁ * ξ) := by
      simp only [ρ]; noncomm_ring
    rw [this, hC, one_mul]
  refine ⟨h1, ?_, ?_⟩
  · have e1 : χ₁ * Q * Gq ^ 2 * Qs * (χ₁ * ξ) = χ₁ * Xq * (χ₁ * ξ) := by
      calc χ₁ * Q * Gq ^ 2 * Qs * (χ₁ * ξ) = (χ₁ * Q) * Gq ^ 2 * (Qs * χ₁) * ξ := by noncomm_ring
        _ = (χ₁ * Qq) * Gq ^ 2 * (Qsq * χ₁) * ξ := by rw [hQ, hQs]
        _ = χ₁ * Xq * (χ₁ * ξ) := by simp only [Xq]; noncomm_ring
    have e2 : ν = χ₁ * (Xq * ξ) := by simp only [Xq, ξ]; rw [hXq, hν]
    have e : -(χ₁ * Xq * ((1 - χ₁) * ξ)) + χ₁ * Q * (G' ^ 2 - Gq ^ 2) * Qs * (χ₁ * ξ) +
        (1 - χ₁) * X * (χ₁ * ξ) = X * (χ₁ * ξ) - χ₁ * (Xq * ξ) +
          (χ₁ * Xq * (χ₁ * ξ) - χ₁ * Q * Gq ^ 2 * Qs * (χ₁ * ξ)) := by
      simp only [X]; noncomm_ring
    rw [e, e1, sub_self, add_zero, ← e2]
  · have : χ * (χ₁ * ξ) = χ * ξ := by rw [← mul_assoc, hχ]
    rw [mul_sub, ← this, h1]; noncomm_ring

/-- `lem:projection-difference`(iii), the decomposition of the proof: with `P = G'Q'^*CQ'G'`,
`P_□ = G'_□Q'^*_□C_□Q'_□G'_□`, `χQ' = χQ'_□`, `Q'^*χ = Q'^*_□χ`, and differences `𝒟`, `𝒟'`
on both sides, `𝒟(P - P_□)𝒟'` is the sum of the five terms of the proof. -/
theorem projection_difference (Q Qs G' C Qq Qsq Gq Cq χ 𝒟 𝒟' : R)
    (hQ : χ * Q = χ * Qq) (hQs : Qs * χ = Qsq * χ) :
    𝒟 * (G' * Qs * C * Q * G' - Gq * Qsq * Cq * Qq * Gq) * 𝒟' =
      𝒟 * (G' - Gq) * Qs * χ * C * χ * Q * G' * 𝒟' +
        𝒟 * Gq * Qs * χ * (C - Cq) * χ * Q * G' * 𝒟' +
        𝒟 * Gq * Qs * χ * Cq * χ * Q * (G' - Gq) * 𝒟' +
        𝒟 * G' * Qs * ((1 - χ) * C + χ * C * (1 - χ)) * Q * G' * 𝒟' -
        𝒟 * Gq * Qsq * ((1 - χ) * Cq + χ * Cq * (1 - χ)) * Qq * Gq * 𝒟' := by
  have e : 𝒟 * Gq * Qsq * (χ * Cq * χ) * Qq * Gq * 𝒟' = 𝒟 * Gq * Qs * (χ * Cq * χ) * Q * Gq * 𝒟' := by
    calc 𝒟 * Gq * Qsq * (χ * Cq * χ) * Qq * Gq * 𝒟' = 𝒟 * Gq * (Qsq * χ) * Cq * (χ * Qq) * Gq * 𝒟' := by
          noncomm_ring
      _ = 𝒟 * Gq * (Qs * χ) * Cq * (χ * Q) * Gq * 𝒟' := by rw [hQ, hQs]
      _ = 𝒟 * Gq * Qs * (χ * Cq * χ) * Q * Gq * 𝒟' := by noncomm_ring
  have split : 𝒟 * Gq * Qsq * Cq * Qq * Gq * 𝒟' =
      𝒟 * Gq * Qsq * (χ * Cq * χ) * Qq * Gq * 𝒟' +
        𝒟 * Gq * Qsq * ((1 - χ) * Cq + χ * Cq * (1 - χ)) * Qq * Gq * 𝒟' := by noncomm_ring
  calc 𝒟 * (G' * Qs * C * Q * G' - Gq * Qsq * Cq * Qq * Gq) * 𝒟' =
        𝒟 * G' * Qs * C * Q * G' * 𝒟' - 𝒟 * Gq * Qsq * Cq * Qq * Gq * 𝒟' := by noncomm_ring
    _ = 𝒟 * G' * Qs * C * Q * G' * 𝒟' - (𝒟 * Gq * Qs * (χ * Cq * χ) * Q * Gq * 𝒟' +
          𝒟 * Gq * Qsq * ((1 - χ) * Cq + χ * Cq * (1 - χ)) * Qq * Gq * 𝒟') := by rw [split, e]
    _ = _ := by noncomm_ring

end Algebra

/-! ### The series and the symmetric form of the inverse -/

section Series

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/-- `thm:walks`(ii): if `A G_0 = I - R` with `‖R‖ < 1` on a space of finite dimension, then `A` is
invertible and `A^{-1} = G_0 Σ_n R^n`. With `first_remainder_block` and `first_remainder_G` this is
the series of the block inverse and of `G`. -/
theorem inverse_of_remainder (A G₀ Rm : V →L[ℂ] V) (hA : A * G₀ = 1 - Rm) (hR : ‖Rm‖ < 1) :
    IsUnit A ∧ Ring.inverse A = G₀ * ∑' n : ℕ, Rm ^ n := by
  have hsum : Summable fun n : ℕ => Rm ^ n := summable_geometric_of_norm_lt_one hR
  have hinv := (WalkProduct.one_sub_inverse Rm hsum).2.1
  have hright : A * (G₀ * ∑' n : ℕ, Rm ^ n) = 1 := by rw [← mul_assoc, hA, hinv]
  obtain ⟨-, hleft⟩ := WalksG.isUnit_of_mul_eq_one hright
  let u : (V →L[ℂ] V)ˣ := ⟨A, G₀ * ∑' n : ℕ, Rm ^ n, hright, hleft⟩
  exact ⟨u.isUnit, Ring.inverse_unit u⟩

end Series

section Transpose

variable {R : Type*} [Ring R]

/-- `thm:walks`, the proof on `G`: for a transposition `τ` (a ring antihomomorphism), if `A` is
symmetric with the right inverse `G = G_0 S`, and `G_0` is symmetric, then `G = S^T G_0`. -/
theorem inverse_transposed (τ : R →+* Rᵐᵒᵖ) (A G G₀ S : R) (hA : (τ A).unop = A)
    (hG₀ : (τ G₀).unop = G₀) (hAG : A * G = 1) (hG : G = G₀ * S) :
    G = (τ S).unop * G₀ := by
  have hτG : (τ G).unop = G := by
    have h1 : (τ G).unop * A = 1 := by
      have := congrArg (fun x => (τ x).unop) hAG
      simpa [hA] using this
    calc (τ G).unop = (τ G).unop * (A * G) := by rw [hAG, mul_one]
      _ = ((τ G).unop * A) * G := by rw [mul_assoc]
      _ = G := by rw [h1, one_mul]
  calc G = (τ G).unop := hτG.symm
    _ = (τ S).unop * (τ G₀).unop := by rw [hG, map_mul, MulOpposite.unop_mul]
    _ = (τ S).unop * G₀ := by rw [hG₀]

end Transpose

end WalkIdentities
end CoreLean
