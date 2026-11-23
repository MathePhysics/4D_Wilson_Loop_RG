/-
Hypothesis (b) of `lem:kernel-inverse` of BALABAN_CORE.tex for `𝔤 ⊂ 𝔤^c`: `coercive_of_real`
instantiated with `V = 𝔤^c` (the subspace `lieCE` of `ℂ^{N×N}`, `Projection.lean`) and `W = 𝔤`.

The scalar product of `ℂ^{N×N}` is `N` times the core's `⟨X, Y⟩ = tr X^* Y`, on both sides of
`Re⟨μ, T₀μ⟩ ≥ γ‖μ‖²`, so that the constant `γ` is the core's.
-/
import CoreLean.KernelInverse
import CoreLean.Projection

open Matrix Complex

namespace CoreLean

variable {N : ℕ} {G : GaugeGroup N}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "EN" => EuclideanSpace ℂ (Fin N × Fin N)

/-- `𝔤` inside `𝔤^c`. -/
def lieW (hG : G.LieInput) : Set (lieCE hG) := {v | flat.symm (v : EN) ∈ G.lie}

/-- `tr AB` is real for Hermitean `A`, `B`. -/
lemma im_trace_mul_herm {A B : Mat} (hA : Aᴴ = A) (hB : Bᴴ = B) : (A * B).trace.im = 0 := by
  have h : star (A * B).trace = (A * B).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA, hB, Matrix.trace_mul_comm]
  exact Complex.conj_eq_iff_im.1 h

/-- The scalar product is real on `𝔤`. -/
lemma lieW_inner_im (hG : G.LieInput) :
    ∀ v ∈ lieW hG, ∀ w ∈ lieW hG, (inner ℂ v w).im = 0 := by
  intro v hv w hw
  have h := inner_flat (flat.symm (v : EN)) (flat.symm (w : EN))
  simp only [LinearEquiv.apply_symm_apply] at h
  rw [Submodule.coe_inner, h, hv.1]
  exact im_trace_mul_herm hv.1 hw.1

/-- `𝔤^c = 𝔤 + i𝔤`. -/
lemma lieW_dec (hG : G.LieInput) :
    ∀ v : lieCE hG, ∃ x ∈ lieW hG, ∃ y ∈ lieW hG, v = x + Complex.I • y := by
  intro v
  obtain ⟨A, hA, B, hB, hAB⟩ := (mem_lieCE' hG).1 v.2
  refine ⟨⟨flat A, (mem_lieCE hG).2 (GaugeGroup.lie_subset_lieC hA)⟩, by simpa [lieW] using hA,
    ⟨flat B, (mem_lieCE hG).2 (GaugeGroup.lie_subset_lieC hB)⟩, by simpa [lieW] using hB, ?_⟩
  ext1
  simp only [Submodule.coe_add, Submodule.coe_smul]
  rw [← map_smul, ← map_add, ← hAB, LinearEquiv.apply_symm_apply]

set_option synthInstance.maxHeartbeats 400000 in
/-- Hypothesis (b) of `lem:kernel-inverse` for `𝔤 ⊂ 𝔤^c`: if `T₀` maps `𝔤`-valued functions to
`𝔤`-valued functions and `Re⟨μ, T₀μ⟩ ≥ γ‖μ‖²` for `𝔤`-valued `μ`, then this holds for all
`𝔤^c`-valued `μ`. -/
theorem coercive_lie (hG : G.LieInput) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T0 : ι → ι → (lieCE hG →L[ℂ] lieCE hG))
    (hT : ∀ μ : L2 ι (lieCE hG), (∀ c, μ.ofLp c ∈ lieW hG) →
      ∀ c, (kerApply T0 μ).ofLp c ∈ lieW hG)
    {γ : ℝ} (hpos : ∀ μ : L2 ι (lieCE hG), (∀ c, μ.ofLp c ∈ lieW hG) →
      γ * ‖μ‖ ^ 2 ≤ RCLike.re (inner ℂ μ (kerApply T0 μ)))
    (μ : L2 ι (lieCE hG)) : γ * ‖μ‖ ^ 2 ≤ RCLike.re (inner ℂ μ (kerApply T0 μ)) := by
  have h1 := coercive_of_real (ι := ι) (V := lieCE hG) (lieW hG) (lieW_inner_im hG)
    (lieW_dec hG) T0
  exact h1 hT hpos μ

end CoreLean
