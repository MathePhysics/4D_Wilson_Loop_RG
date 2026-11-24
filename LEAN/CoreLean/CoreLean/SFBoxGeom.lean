/-
The step "The box" of the proof of `lem:sf-local` of BALABAN_CORE.tex (`4252790331fd`) on the fine lattice of a
sequence of domains (`SeqDom`), in the units `a₀ = 1`, with the box `Q_ρ` of a site `x` of the scale `j ≥ 1` in the
coordinates of the layer (`ε = L^{-j}`, `x̄ = (x_ν mod N₀)_ν ∈ ℤ⁴`).

* `RegField`: the bounds of the field `X = a₀A'` which `prop:sf-scalar` derives from `eq:regular-complex`, in the units
  `a₀ = 1`: `‖X(b)‖ ≤ α₁L^{-i}` on the bonds with both ends in `Ω_i`, and `‖X_μ(z + e_ν) - X_μ(z)‖ ≤ α₁L^{-2i}` when
  `z, z + e_ν ∈ Ω_i` (the core's `‖A'(b)‖ ≤ α₁a_i⁻¹` and `‖∂_νA'_μ‖ ≤ α₁a_i⁻²`).
* `dinf_castS_le`: the sites under `Q_ρ` lie within `ρLʲ` of `x`; `box_mem_Ω`: for `RM ≥ 8L²` and `ρ ≤ 9 + 2L` they
  lie in `Ω_{j-1}` (`eq:separation`), and their scales are at most `j + 1` (`box_sc_le`).
* `fieldHyp_of`: the hypotheses `FieldHyp` of `lem:sf-local` for the field of the layer `Ã = LʲX`:
  `‖Ã‖ ≤ α₁L` and `‖Ã(n + e_ν) - Ã(n)‖ ≤ εα₁L²` on `Q_{8+2L}`.
-/
import CoreLean.SFBox
import CoreLean.SFGeometry

open Finset Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace SFBox

open SFLocal LocalLaplacian InteriorSchauder Lattices Blocks SmallFieldBlocks

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ

/-- The lift `x̄ ∈ ℤ⁴` of a site. -/
def xbar {n : ℕ} (x : Site n) : Fin 4 → ℤ := fun ν => ((x ν).val : ℤ)

lemma castS_xbar {n : ℕ} [NeZero n] (x : Site n) : castS (xbar x) = x := by
  funext ν; simp [castS, xbar]

/-- **The sites under `Q_ρ` lie within `ρLʲ` of `x`.** -/
lemma dinf_castS_le {n : ℕ} [NeZero n] {a ρ : ℝ} (ha : 0 < a) (x : Site n) {z : Fin 4 → ℤ}
    (hz : InQr a⁻¹ (xbar x) ρ z) : (dinf (castS z) x : ℝ) ≤ ρ * a := by
  have key : ∀ ν, (cd (castS z ν - x ν) : ℝ) ≤ ρ * a := fun ν => by
    have h := hz ν
    unfold tc at h
    rw [abs_mul, abs_of_pos (inv_pos.2 ha), inv_mul_le_iff₀ ha] at h
    have e : castS (n := n) z ν - x ν = (((z ν - xbar x ν) : ℤ) : ZMod n) := by
      simp [castS, xbar]
    rw [e]
    calc (cd (((z ν - xbar x ν) : ℤ) : ZMod n) : ℝ) ≤ ((z ν - xbar x ν).natAbs : ℝ) := by
          exact_mod_cast cd_intCast_le _
      _ = |((z ν - xbar x ν : ℤ) : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
      _ ≤ ρ * a := by rw [mul_comm]; exact h
  obtain ⟨ν, -, hν⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (fun ν => cd (castS (n := n) z ν - x ν))
  have : dinf (castS z) x = cd (castS (n := n) z ν - x ν) := hν
  rw [this]; exact key ν

lemma inQr_add_e4 {ε ρ : ℝ} (hε : 0 < ε) {z₀ z : Fin 4 → ℤ} (hz : InQr ε z₀ ρ z) (μ : Fin 4) :
    InQr ε z₀ (ρ + ε) (z + e4 μ) := fun ν => by
  have h := hz ν
  unfold tc at h ⊢
  have e : ((((z + e4 μ) ν - z₀ ν : ℤ)) : ℝ) = ((z ν - z₀ ν : ℤ) : ℝ) + (e4 μ ν : ℝ) := by
    simp only [Pi.add_apply]; push_cast; ring
  rw [e, mul_add]
  refine (abs_add_le _ _).trans ?_
  have h1 : |ε * (e4 μ ν : ℝ)| ≤ ε := by
    simp only [e4]
    by_cases hν : ν = μ
    · subst hν; simp [abs_of_pos hε]
    · simp [Pi.single_eq_of_ne hν, hε.le]
  linarith

namespace SeqDomBox

variable (S : SeqDom)

local notation "NF" => SequenceAverages.N0 S
local notation "RMS" => ((S.R * S.L ^ S.mM : ℕ) : ℝ)

/-- The bounds of the field `X = a₀A'` in the units `a₀ = 1`. -/
structure RegField (X : Fin 4 → Site NF → Mat) (α₁ : ℝ) : Prop where
  hA : ∀ i x μ, S.ef x ∈ S.Ω i → S.ef (x + unit _ μ) ∈ S.Ω i → ‖X μ x‖ ≤ α₁ * ((S.L : ℝ) ^ i)⁻¹
  hdA : ∀ i x μ ν, S.ef x ∈ S.Ω i → S.ef (x + unit _ ν) ∈ S.Ω i →
    ‖X μ (x + unit _ ν) - X μ x‖ ≤ α₁ * ((S.L : ℝ) ^ (2 * i))⁻¹

lemma L_pos' : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos

lemma L3 : (3 : ℝ) ≤ S.L := by exact_mod_cast S.three_le_L

/-- **The sites under `Q_ρ`, `ρ ≤ 9 + 2L`, lie in `Ω_{j-1}`** once `RM ≥ 8L²`. -/
theorem box_mem_Ω (hRM : 8 * (S.L : ℝ) ^ 2 ≤ RMS) (x : Site NF) {ρ : ℝ} (hρ : ρ ≤ 9 + 2 * S.L) {z : Fin 4 → ℤ}
    (hz : InQr ((S.L : ℝ) ^ (S.toDomSeq).sc x)⁻¹ (xbar x) ρ z) :
    S.ef (castS z) ∈ S.Ω ((S.toDomSeq).sc x - 1) := by
  have hL := L3 S
  have hd := dinf_castS_le (by positivity) x hz
  refine S.layer_bonds_i (c := 10 + 2 * S.L) (by nlinarith) ((S.toDomSeq).sc_le x) (S.ef_mem_sc x) ?_
  rw [dist_eq_norm, norm_emb_sub S.Lpos (SequenceAverages.N0_eq S)]
  have he := eta_pos (k := S.k) S.Lpos
  unfold sp
  have hp : (0 : ℝ) < (S.L : ℝ) ^ (S.toDomSeq).sc x := by positivity
  have h1 : (dinf (castS z) x : ℝ) < (10 + 2 * S.L) * (S.L : ℝ) ^ (S.toDomSeq).sc x := by nlinarith
  calc (dinf (castS z) x : ℝ) * eta S.L S.k < (10 + 2 * S.L) * (S.L : ℝ) ^ (S.toDomSeq).sc x * eta S.L S.k :=
        mul_lt_mul_of_pos_right h1 he
    _ = _ := by ring

/-- **The scales of the sites under `Q_ρ`, `ρ ≤ 9 + 2L`, are at most `j + 1`.** -/
theorem box_sc_le (hRM : 8 * (S.L : ℝ) ^ 2 ≤ RMS) (x : Site NF) {ρ : ℝ} (hρ : ρ ≤ 9 + 2 * S.L)
    {z : Fin 4 → ℤ} (hz : InQr ((S.L : ℝ) ^ (S.toDomSeq).sc x)⁻¹ (xbar x) ρ z) :
    (S.toDomSeq).sc (castS z) ≤ (S.toDomSeq).sc x + 1 := by
  have hL := L3 S
  have hRM1 : 1 ≤ S.R * S.L ^ S.mM := by have := Nat.one_le_pow S.mM S.L S.Lpos; nlinarith [S.one_le_R]
  refine S.sc_le_succ_of_near hRM1 ?_
  rw [dinf_comm]
  have hd := dinf_castS_le (by positivity) x hz
  have hp : (0 : ℝ) < (S.L : ℝ) ^ (S.toDomSeq).sc x := by positivity
  have h1 : ρ * (S.L : ℝ) ^ (S.toDomSeq).sc x ≤ (9 + 2 * S.L) * (S.L : ℝ) ^ (S.toDomSeq).sc x :=
    mul_le_mul_of_nonneg_right hρ hp.le
  have h2 : (9 + 2 * (S.L : ℝ)) ≤ RMS := by nlinarith
  have h3 := mul_le_mul_of_nonneg_right h2 hp.le
  linarith

/-- **The hypotheses of `lem:sf-local` on the field of the layer.** -/
theorem fieldHyp_of {X : Fin 4 → Site NF → Mat} {α₁ : ℝ} (hX : RegField S X α₁) (hα0 : 0 ≤ α₁)
    (hα : 64 * (S.L : ℝ) ^ 2 * α₁ ≤ 1) (hRM : 8 * (S.L : ℝ) ^ 2 ≤ RMS) (x : Site NF)
    (hj : 1 ≤ (S.toDomSeq).sc x) :
    FieldHyp ((S.L : ℝ) ^ (S.toDomSeq).sc x)⁻¹ (xbar x) (Atil ((S.L : ℝ) ^ (S.toDomSeq).sc x) X) S.L α₁ := by
  set j := (S.toDomSeq).sc x
  have hL := L3 S
  have hL1 : (1 : ℝ) ≤ S.L := by linarith
  have hp : (0 : ℝ) < (S.L : ℝ) ^ j := by positivity
  have hε : 0 < ((S.L : ℝ) ^ j)⁻¹ := inv_pos.2 hp
  have hεle : ((S.L : ℝ) ^ j)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hL1)
  have hpow1 : (S.L : ℝ) ^ j = S.L * (S.L : ℝ) ^ (j - 1) := by rw [← pow_succ', Nat.sub_add_cancel hj]
  refine ⟨hε, ?_, hL, hα0, hα, ?_, ?_⟩
  · rw [inv_le_comm₀ hp (by norm_num), inv_div, div_one]
    calc (3 : ℝ) ≤ S.L := hL
      _ = (S.L : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (S.L : ℝ) ^ j := pow_le_pow_right₀ hL1 hj
  · intro μ z hz
    have hz' : InQr ((S.L : ℝ) ^ j)⁻¹ (xbar x) (8 + 2 * S.L + 1) (z + e4 μ) :=
      fun ν => ((inQr_add_e4 hε hz μ) ν).trans (by linarith)
    have h1 := box_mem_Ω S hRM x (by linarith) hz
    have h2 := box_mem_Ω S hRM x (by linarith) hz'
    rw [castS_add_e4] at h2
    have hb := hX.hA (j - 1) (castS z) μ h1 h2
    simp only [Atil]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hp]
    calc (S.L : ℝ) ^ j * ‖X μ (castS z)‖ ≤ (S.L : ℝ) ^ j * (α₁ * ((S.L : ℝ) ^ (j - 1))⁻¹) :=
          mul_le_mul_of_nonneg_left hb hp.le
      _ = α₁ * S.L * ((S.L : ℝ) ^ (j - 1) * ((S.L : ℝ) ^ (j - 1))⁻¹) := by rw [hpow1]; ring
      _ = α₁ * S.L := by rw [mul_inv_cancel₀ (by positivity), mul_one]
  · intro μ ν z hz hz'
    have h1 := box_mem_Ω S hRM x (by linarith) hz
    have h2 := box_mem_Ω S hRM x (by linarith) hz'
    rw [castS_add_e4] at h2
    have hb := hX.hdA (j - 1) (castS z) μ ν h1 h2
    simp only [Atil]
    rw [castS_add_e4, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hp]
    have e2 : (S.L : ℝ) ^ j * (S.L : ℝ) ^ j = (S.L : ℝ) ^ (2 * (j - 1)) * S.L ^ 2 := by
      rw [hpow1, pow_mul]; ring
    have hq : (S.L : ℝ) ^ (2 * (j - 1)) ≠ 0 := by positivity
    calc (S.L : ℝ) ^ j * ‖X μ (castS z + unit _ ν) - X μ (castS z)‖
        ≤ (S.L : ℝ) ^ j * (α₁ * ((S.L : ℝ) ^ (2 * (j - 1)))⁻¹) := mul_le_mul_of_nonneg_left hb hp.le
      _ = ((S.L : ℝ) ^ j)⁻¹ * (α₁ * S.L ^ 2) := by
        rw [eq_inv_mul_iff_mul_eq₀ hp.ne']
        calc (S.L : ℝ) ^ j * ((S.L : ℝ) ^ j * (α₁ * ((S.L : ℝ) ^ (2 * (j - 1)))⁻¹))
            = (S.L : ℝ) ^ j * (S.L : ℝ) ^ j * (α₁ * ((S.L : ℝ) ^ (2 * (j - 1)))⁻¹) := by ring
          _ = α₁ * S.L ^ 2 * ((S.L : ℝ) ^ (2 * (j - 1)) * ((S.L : ℝ) ^ (2 * (j - 1)))⁻¹) := by rw [e2]; ring
          _ = α₁ * S.L ^ 2 := by rw [mul_inv_cancel₀ hq, mul_one]

end SeqDomBox
end SFBox
end CoreLean

end
