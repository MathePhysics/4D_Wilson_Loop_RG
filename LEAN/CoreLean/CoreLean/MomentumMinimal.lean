/-
`prop:momentum-space`(iv) of BALABAN_CORE.tex (`fc142d786d90`), the minimisation on one fibre `{p' + l}_l`. For a finite
family of vectors `∂(l) ∈ ℂ⁴` with `Δ(l) = |∂(l)|² > 0`, weights `w_μ(l)` with `w_μ(l)∂_μ(l) = u(l)∂¹_μ` (`u` real), and
`φ_μ = Σ_l|w_μ(l)|²/Δ(l) > 0`, `S = Σ_λ|∂¹_λ|²/φ_λ > 0`, `u(l₀) ≠ 0`: the minimum of
`F(a) = ½Σ_{μ,ν}Σ_l|∂_μ(l)a_ν(l) - ∂_ν(l)a_μ(l)|²` under `Σ_lw_μ(l)a_μ(l) = b_μ` is
`½Σ_{μ,ν}|∂¹_μb_ν - ∂¹_νb_μ|²/(Sφ_μφ_ν)`.

The proof is by a dual vector instead of the core's limit `ε → 0`: for `c ⊥ ∂¹` the vectors `v(l) = W(l)*c` are orthogonal to
`∂(l)`, and `a*H₀a ≥ 2 Re v*a - |v|²/Δ` gives `F(a) ≥ 2 Re c*b - c*Φc`; with `c = Φ⁻¹(b - τ∂¹)`, `τ = (∂¹)*Φ⁻¹b/S`, this is the
value. It is attained at `a(l) = v(l)/Δ(l) + α(l)∂(l)`, `α(l₀)u(l₀) = τ`, on which `F` does not see the multiples of `∂(l)`.
-/
import Mathlib

open Complex

noncomputable section

namespace CoreLean
namespace MomentumMinimal

/-- **The weighted Lagrange identity**:
`½Σ_{μ,ν}ρ_μρ_ν|x_μy_ν - x_νy_μ|² = (Σρ_μ|x_μ|²)(Σρ_μ|y_μ|²) - |Σρ_μ x̄_μy_μ|²`. -/
lemma lagrange_w (ρ : Fin 4 → ℝ) (x y : Fin 4 → ℂ) :
    1 / 2 * ∑ μ, ∑ ν, ρ μ * ρ ν * ‖x μ * y ν - x ν * y μ‖ ^ 2 =
      (∑ μ, ρ μ * ‖x μ‖ ^ 2) * (∑ μ, ρ μ * ‖y μ‖ ^ 2) -
        ‖∑ μ, (ρ μ : ℂ) * (starRingEnd ℂ (x μ) * y μ)‖ ^ 2 := by
  simp only [Fin.sum_univ_four, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- `|x|² = Σ_μ|x_μ|²`. -/
def nsq (x : Fin 4 → ℂ) : ℝ := ∑ μ, ‖x μ‖ ^ 2

/-- `x*y = Σ_μ x̄_μy_μ`. -/
def ip (x y : Fin 4 → ℂ) : ℂ := ∑ μ, starRingEnd ℂ (x μ) * y μ

lemma nsq_nonneg (x : Fin 4 → ℂ) : 0 ≤ nsq x := Finset.sum_nonneg fun _ _ => by positivity

lemma conj_mul_self' (z : ℂ) : starRingEnd ℂ z * z = (‖z‖ : ℂ) ^ 2 := by
  rw [← Complex.ofReal_pow, Complex.sq_norm, Complex.normSq_eq_conj_mul_self]

lemma mul_conj' (z : ℂ) : z * starRingEnd ℂ z = (‖z‖ : ℂ) ^ 2 := by
  rw [mul_comm, conj_mul_self']

/-- The Lagrange identity. -/
lemma lagrange (x y : Fin 4 → ℂ) :
    1 / 2 * ∑ μ, ∑ ν, ‖x μ * y ν - x ν * y μ‖ ^ 2 = nsq x * nsq y - ‖ip x y‖ ^ 2 := by
  have h := lagrange_w (fun _ => 1) x y
  simp only [one_mul, Complex.ofReal_one] at h
  exact h

/-- The Cauchy–Schwarz inequality, from the Lagrange identity. -/
lemma cs (x y : Fin 4 → ℂ) : ‖ip x y‖ ^ 2 ≤ nsq x * nsq y := by
  have h := lagrange x y
  have h0 : 0 ≤ 1 / 2 * ∑ μ, ∑ ν, ‖x μ * y ν - x ν * y μ‖ ^ 2 := by positivity
  linarith

/-- **`a*H₀a ≥ 2 Re v*a - |v|²/Δ` for `v ⊥ ∂`**, `H₀ = ΔI - ∂∂*`, `Δ = |∂|²`: Cauchy–Schwarz at `a - v/Δ`. -/
lemma key (D a v : Fin 4 → ℂ) (hD : 0 < nsq D) (hv : ip D v = 0) :
    2 * (ip v a).re - nsq v / nsq D ≤ nsq D * nsq a - ‖ip D a‖ ^ 2 := by
  set c : ℝ := 1 / nsq D with hc
  set y : Fin 4 → ℂ := fun μ => a μ - (c : ℂ) * v μ with hy
  have h1 := cs D y
  have hip : ip D y = ip D a := by
    have e : ip D y = ip D a - (c : ℂ) * ip D v := by
      simp only [ip, hy, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun μ _ => by ring
    rw [e, hv, mul_zero, sub_zero]
  have hny : nsq y = nsq a - 2 * c * (ip v a).re + c ^ 2 * nsq v := by
    simp only [nsq, ip, hy, Fin.sum_univ_four, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.conj_re,
      Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hip, hny] at h1
  have e : nsq D * (nsq a - 2 * c * (ip v a).re + c ^ 2 * nsq v) =
      nsq D * nsq a - 2 * (ip v a).re + nsq v / nsq D := by
    rw [hc]; field_simp
  linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section Fibre

variable (D w : ι → Fin 4 → ℂ) (d b : Fin 4 → ℂ)

/-- `F(a) = ½Σ_lΣ_{μ,ν}|∂_μ(l)a_ν(l) - ∂_ν(l)a_μ(l)|²`. -/
def Fq (a : ι → Fin 4 → ℂ) : ℝ := 1 / 2 * ∑ l, ∑ μ, ∑ ν, ‖D l μ * a l ν - D l ν * a l μ‖ ^ 2

/-- `φ_μ = Σ_l|w_μ(l)|²/Δ(l)`. -/
def phiF (μ : Fin 4) : ℝ := ∑ l, ‖w l μ‖ ^ 2 / nsq (D l)

/-- `S = Σ_λ|∂¹_λ|²/φ_λ`. -/
def SF : ℝ := ∑ μ, ‖d μ‖ ^ 2 / phiF D w μ

/-- The value `½Σ_{μ,ν}|∂¹_μb_ν - ∂¹_νb_μ|²/(Sφ_μφ_ν)`. -/
def VF : ℝ := 1 / 2 * ∑ μ, ∑ ν, ‖d μ * b ν - d ν * b μ‖ ^ 2 / (SF D w d * phiF D w μ * phiF D w ν)

/-- The constraint `Σ_lw_μ(l)a_μ(l) = b_μ`. -/
def Adm (a : ι → Fin 4 → ℂ) : Prop := ∀ μ, ∑ l, w l μ * a l μ = b μ

end Fibre

lemma Fq_eq (D a : ι → Fin 4 → ℂ) : Fq D a = ∑ l, (nsq (D l) * nsq (a l) - ‖ip (D l) (a l)‖ ^ 2) := by
  unfold Fq
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => lagrange _ _

/-- `V = Σ_μ|b_μ|²/φ_μ - |Σ_μ∂̄¹_μb_μ/φ_μ|²/S`, the weighted Lagrange identity. -/
lemma VF_eq (D w : ι → Fin 4 → ℂ) (d b : Fin 4 → ℂ) (hφ : ∀ μ, 0 < phiF D w μ) (hS : 0 < SF D w d) :
    VF D w d b = (∑ μ, ‖b μ‖ ^ 2 / phiF D w μ) -
      ‖∑ μ, starRingEnd ℂ (d μ) * b μ / (phiF D w μ : ℂ)‖ ^ 2 / SF D w d := by
  have h := lagrange_w (fun μ => 1 / phiF D w μ) d b
  have hterm : ∀ μ ν, ‖d μ * b ν - d ν * b μ‖ ^ 2 / (SF D w d * phiF D w μ * phiF D w ν) =
      1 / SF D w d * (1 / phiF D w μ * (1 / phiF D w ν) * ‖d μ * b ν - d ν * b μ‖ ^ 2) := by
    intro μ ν
    have := hφ μ; have := hφ ν
    field_simp
  have e1 : VF D w d b = 1 / SF D w d *
      (1 / 2 * ∑ μ, ∑ ν, 1 / phiF D w μ * (1 / phiF D w ν) * ‖d μ * b ν - d ν * b μ‖ ^ 2) := by
    unfold VF
    simp only [hterm, ← Finset.mul_sum]
    ring
  rw [e1, h]
  have e2 : ∑ μ, 1 / phiF D w μ * ‖d μ‖ ^ 2 = SF D w d := by
    unfold SF; exact Finset.sum_congr rfl fun μ _ => by ring
  have e3 : ∑ μ, 1 / phiF D w μ * ‖b μ‖ ^ 2 = ∑ μ, ‖b μ‖ ^ 2 / phiF D w μ :=
    Finset.sum_congr rfl fun μ _ => by ring
  have e4 : ∑ μ, ((1 / phiF D w μ : ℝ) : ℂ) * (starRingEnd ℂ (d μ) * b μ) =
      ∑ μ, starRingEnd ℂ (d μ) * b μ / (phiF D w μ : ℂ) :=
    Finset.sum_congr rfl fun μ _ => by push_cast; ring
  rw [e2, e3, e4]
  field_simp

/-- **The minimum on one fibre** (`prop:momentum-space`(iv)): under `Σ_lw_μ(l)a_μ(l) = b_μ`, `F(a)` is at least
`V = ½Σ_{μ,ν}|∂¹_μb_ν - ∂¹_νb_μ|²/(Sφ_μφ_ν)`, and `V` is attained. -/
theorem fibre_min (D w : ι → Fin 4 → ℂ) (d b : Fin 4 → ℂ) (u : ι → ℝ) (hΔ : ∀ l, 0 < nsq (D l))
    (hφ : ∀ μ, 0 < phiF D w μ) (hS : 0 < SF D w d) (hwd : ∀ l μ, w l μ * D l μ = (u l : ℂ) * d μ) (l0 : ι)
    (hu0 : u l0 ≠ 0) :
    (∀ a, Adm w b a → VF D w d b ≤ Fq D a) ∧ ∃ a, Adm w b a ∧ Fq D a = VF D w d b := by
  have hφC : ∀ μ, (phiF D w μ : ℂ) ≠ 0 := fun μ => Complex.ofReal_ne_zero.2 (hφ μ).ne'
  have hSC : (SF D w d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hS.ne'
  have hΔC : ∀ l, (nsq (D l) : ℂ) ≠ 0 := fun l => Complex.ofReal_ne_zero.2 (hΔ l).ne'
  set φ := phiF D w with hφdef
  set S := SF D w d with hSdef
  set P : ℂ := ∑ μ, starRingEnd ℂ (d μ) * b μ / (φ μ : ℂ) with hP
  set τ : ℂ := P / S with hτ
  set c : Fin 4 → ℂ := fun μ => (b μ - τ * d μ) / (φ μ : ℂ) with hc
  set v : ι → Fin 4 → ℂ := fun l μ => starRingEnd ℂ (w l μ) * c μ with hv
  set Q : ℝ := ∑ μ, φ μ * ‖c μ‖ ^ 2 with hQ
  -- `c ⊥ ∂¹`
  have hdc : ip d c = 0 := by
    have hS' : (S : ℂ) = ∑ μ, starRingEnd ℂ (d μ) * d μ / (φ μ : ℂ) := by
      rw [hSdef]; unfold SF; push_cast
      exact Finset.sum_congr rfl fun μ _ => by rw [conj_mul_self']
    have e : ip d c = P - τ * S := by
      rw [hS', Finset.mul_sum, hP, ← Finset.sum_sub_distrib]
      unfold ip
      exact Finset.sum_congr rfl fun μ _ => by simp only [hc]; have := hφC μ; field_simp
    rw [e, hτ]; field_simp; ring
  -- `v(l) ⊥ ∂(l)`
  have hDv : ∀ l, ip (D l) (v l) = 0 := by
    intro l
    have e : ip (D l) (v l) = (u l : ℂ) * ip d c := by
      unfold ip
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun μ _ => ?_
      have h := congrArg (starRingEnd ℂ) (hwd l μ)
      simp only [map_mul, Complex.conj_ofReal] at h
      calc starRingEnd ℂ (D l μ) * v l μ = (starRingEnd ℂ (w l μ) * starRingEnd ℂ (D l μ)) * c μ := by
            simp only [hv]; ring
        _ = (u l : ℂ) * (starRingEnd ℂ (d μ) * c μ) := by rw [h]; ring
    rw [e, hdc, mul_zero]
  -- `b = φc + τ∂¹`
  have hb : ∀ μ, b μ = (φ μ : ℂ) * c μ + τ * d μ := fun μ => by
    simp only [hc]; have := hφC μ; field_simp; ring
  -- `c*b = Q`
  have hcb : ip c b = (Q : ℂ) := by
    have e : ip c b = ∑ μ, (φ μ : ℂ) * (starRingEnd ℂ (c μ) * c μ) + τ * starRingEnd ℂ (ip d c) := by
      unfold ip
      simp only [map_sum, map_mul, Complex.conj_conj, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun μ _ => ?_
      conv_lhs => rw [hb μ]
      ring
    rw [e, hdc, map_zero, mul_zero, add_zero, hQ]
    push_cast
    exact Finset.sum_congr rfl fun μ _ => by rw [conj_mul_self']
  -- `Q = V`
  have hQV : Q = VF D w d b := by
    rw [VF_eq D w d b hφ hS]
    have e : ip c b = ((∑ μ, ‖b μ‖ ^ 2 / φ μ : ℝ) : ℂ) - starRingEnd ℂ τ * P := by
      push_cast
      unfold ip
      rw [hP, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun μ _ => ?_
      simp only [hc, map_div₀, map_sub, map_mul, Complex.conj_ofReal]
      have := hφC μ
      rw [← conj_mul_self' (b μ)]
      field_simp
    have e2 : starRingEnd ℂ τ * P = ((‖P‖ ^ 2 / S : ℝ) : ℂ) := by
      rw [hτ, map_div₀, Complex.conj_ofReal]
      push_cast
      rw [← conj_mul_self' P]
      field_simp
    rw [e2, hcb] at e
    exact_mod_cast e
  -- the sums over `l`
  have hsum2 : ∑ l, nsq (v l) / nsq (D l) = Q := by
    simp only [nsq, hv, norm_mul, Complex.norm_conj, mul_pow, Finset.sum_div, hQ]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [hφdef]; unfold phiF; rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by simp only [nsq]; ring
  refine ⟨fun a ha => ?_, ?_⟩
  · -- the lower bound
    rw [Fq_eq, ← hQV]
    have hsum1 : ∑ l, ip (v l) (a l) = ip c b := by
      unfold ip
      simp only [hv, map_mul, Complex.conj_conj]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun μ _ => ?_
      rw [← ha μ, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    calc Q = 2 * (ip c b).re - Q := by rw [hcb, Complex.ofReal_re]; ring
      _ = ∑ l, (2 * (ip (v l) (a l)).re - nsq (v l) / nsq (D l)) := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Complex.re_sum, hsum1, hsum2]
      _ ≤ _ := Finset.sum_le_sum fun l _ => key (D l) (a l) (v l) (hΔ l) (hDv l)
  · -- the minimiser `a(l) = v(l)/Δ(l) + α(l)∂(l)`
    have hu0C : (u l0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hu0
    set α : ι → ℂ := fun l => if l = l0 then τ / (u l0 : ℂ) else 0 with hα
    set a : ι → Fin 4 → ℂ := fun l μ => v l μ / (nsq (D l) : ℂ) + α l * D l μ with ha
    refine ⟨a, fun μ => ?_, ?_⟩
    · have e1 : ∑ l, w l μ * a l μ = c μ * (φ μ : ℂ) + ∑ l, α l * (w l μ * D l μ) := by
        simp only [ha, mul_add, Finset.sum_add_distrib]
        congr 1
        · rw [hφdef]; unfold phiF; push_cast; rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          simp only [hv]
          rw [← mul_conj' (w l μ)]
          have := hΔC l
          field_simp
        · exact Finset.sum_congr rfl fun l _ => by ring
      rw [e1]
      simp only [hwd, hα, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [hb μ]
      field_simp
    · rw [← hQV, ← hsum2]
      have hterm : ∀ l μ ν, ‖D l μ * a l ν - D l ν * a l μ‖ ^ 2 =
          ‖D l μ * v l ν - D l ν * v l μ‖ ^ 2 / nsq (D l) ^ 2 := by
        intro l μ ν
        have e : D l μ * a l ν - D l ν * a l μ = (D l μ * v l ν - D l ν * v l μ) / (nsq (D l) : ℂ) := by
          simp only [ha]; have := hΔC l; field_simp; ring
        rw [e, norm_div, Complex.norm_real, Real.norm_of_nonneg (nsq_nonneg _), div_pow]
      have hl : ∀ l, ∑ μ, ∑ ν, ‖D l μ * v l ν - D l ν * v l μ‖ ^ 2 / nsq (D l) ^ 2 =
          2 * (nsq (v l) / nsq (D l)) := by
        intro l
        have h := lagrange (D l) (v l)
        rw [hDv l, norm_zero] at h
        have h' : ∑ μ, ∑ ν, ‖D l μ * v l ν - D l ν * v l μ‖ ^ 2 = 2 * (nsq (D l) * nsq (v l)) := by linarith
        simp only [← Finset.sum_div]
        rw [h']
        have := hΔ l
        field_simp
      unfold Fq
      simp only [hterm]
      rw [Finset.sum_congr rfl fun l _ => hl l, ← Finset.mul_sum]
      ring

end MomentumMinimal
end CoreLean

end
