/-
**`lem:local-inverse`** of BALABAN_CORE.tex (`a021c13be348`), in the setting of `KernelInverse.lean`: kernels
`ι → ι → (V →L[ℂ] V)` on `L²(ι; V)`, `ι` the set `S` of positive bonds of the layers, `c ↦ c₋` with a pseudometric `d`.
(i) If `‖𝒮[c, c']‖ ≤ εe^{-δ'd(c₋, c'₋)}` and the sums `Σ_{c'}e^{-(δ'/2)d(c₋, c'₋)}` are at most `K'` (the core's
`n_bc₁(½, δ')`, from `eq:summation`), then for `0 ≤ θ ≤ δ'/2` the conjugated operator has the norm `≤ K'ε`
(`local_inverse_i`). (ii) For `S_□ ⊂ S` and `𝒯 = 𝒯₀ + 𝒯₁` as in `lem:kernel-inverse` with `γ/8` in (c), and `E` on the
functions on `S_□` with `‖E[c, c']‖ ≤ εe^{-δ'd}` and `K'ε ≤ γ/8`, the operator `F = 1_{S_□}𝒯1_{S_□} - E` is invertible on
the functions on `S_□` with `‖F⁻¹[c, c']‖ ≤ (2/γ)e^{-θd(c₋, c'₋)}`, `θ = min{θ₀, δ/2, γδ/(6κK)}` (`local_inverse_ii`).
The proof is the core's: the compression keeps (a), the coercivity (b) (`compress_coercive`), and the bound (c)
(`compress_opBound`), `-E` satisfies (c) by (i), and `lem:kernel-inverse` applies on `S_□`.
-/
import CoreLean.KernelInverse

open Real

noncomputable section

namespace CoreLean

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

lemma OpBound.sub {K L : ι → ι → (V →L[ℂ] V)} {a b : ℝ} (hK : OpBound K a) (hL : OpBound L b) :
    OpBound (K - L) (a + b) := fun μ => by
  rw [kerApply_sub]
  refine (norm_sub_le _ _).trans ?_
  have := hK μ; have := hL μ
  linarith

lemma conjKer_sub (θ : ℝ) (ρ : ι → ℝ) (K L : ι → ι → (V →L[ℂ] V)) :
    conjKer θ ρ (K - L) = conjKer θ ρ K - conjKer θ ρ L := by
  funext c c'; simp [conjKer, smul_sub]

/-- **`lem:local-inverse`(i)**: the conjugated operator `e^{θ(ρ(c) - ρ(c'))}𝒮[c, c']` has the norm `≤ K'ε`. -/
theorem local_inverse_i {B : Type*} [PseudoMetricSpace B] (fe : ι → B) {δ' ε K' θ : ℝ} (hε : 0 ≤ ε)
    (hK' : ∀ c, ∑ c', Real.exp (-(δ' / 2) * dist (fe c) (fe c')) ≤ K') (S : ι → ι → (V →L[ℂ] V))
    (hS : ∀ c c', ‖S c c'‖ ≤ ε * Real.exp (-δ' * dist (fe c) (fe c'))) (y : B) (hθ0 : 0 ≤ θ)
    (hθ : θ ≤ δ' / 2) : OpBound (conjKer θ (fun c => dist (fe c) y) S) (K' * ε) := by
  set k : ι → ι → ℝ := fun c c' => ε * Real.exp (-(δ' / 2) * dist (fe c) (fe c'))
  have hk : ∀ c c', ‖conjKer θ (fun c => dist (fe c) y) S c c'‖ ≤ k c c' := fun c c' => by
    simp only [conjKer, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hx : θ * (dist (fe c) y - dist (fe c') y) ≤ θ * dist (fe c) (fe c') :=
      mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) (abs_dist_sub_le _ _ _)) hθ0
    have hd := dist_nonneg (x := fe c) (y := fe c')
    calc Real.exp (θ * (dist (fe c) y - dist (fe c') y)) * ‖S c c'‖
        ≤ Real.exp (θ * dist (fe c) (fe c')) * (ε * Real.exp (-δ' * dist (fe c) (fe c'))) :=
          mul_le_mul (Real.exp_le_exp.2 hx) (hS c c') (norm_nonneg _) (Real.exp_pos _).le
      _ = ε * (Real.exp (θ * dist (fe c) (fe c')) * Real.exp (-δ' * dist (fe c) (fe c'))) := by ring
      _ ≤ ε * Real.exp (-(δ' / 2) * dist (fe c) (fe c')) := by
          refine mul_le_mul_of_nonneg_left ?_ hε
          rw [← Real.exp_add, Real.exp_le_exp]; nlinarith
  have hR : ∀ c, ∑ c', k c c' ≤ ε * K' := fun c => by
    simp only [k]; rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (hK' c) hε
  have hC : ∀ c', ∑ c, k c c' ≤ ε * K' := fun c' => by
    simp only [k]; rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ((Finset.sum_le_sum fun c _ => ?_).trans (hK' c')) hε
    rw [dist_comm]
  have := opBound_of_entry _ k hk hR hC
  rwa [max_self, mul_comm] at this

/-! ### Compression to a subset -/

variable (s : Finset ι)

/-- The compression `1_{S_□}K1_{S_□}` as a kernel on `S_□`. -/
def compress (K : ι → ι → (V →L[ℂ] V)) : s → s → (V →L[ℂ] V) := fun c c' => K c c'

/-- The extension by zero of a function on `S_□`. -/
def extZ (μ : L2 s V) : L2 ι V := WithLp.toLp 2 fun c => if h : c ∈ s then μ.ofLp ⟨c, h⟩ else 0

lemma extZ_apply (μ : L2 s V) (c : ι) :
    (extZ s μ).ofLp c = if h : c ∈ s then μ.ofLp ⟨c, h⟩ else 0 := rfl

lemma extZ_coe (μ : L2 s V) (c : s) : (extZ s μ).ofLp c = μ.ofLp c := by
  rw [extZ_apply, dif_pos c.2]

lemma extZ_out (μ : L2 s V) {c : ι} (hc : c ∉ s) : (extZ s μ).ofLp c = 0 := by
  rw [extZ_apply, dif_neg hc]

lemma sum_extZ {W : Type*} [AddCommMonoid W] (f : ι → W) (hf : ∀ c ∉ s, f c = 0) :
    ∑ c, f c = ∑ c : s, f c := by
  rw [Finset.sum_coe_sort s f]
  exact (Finset.sum_subset (Finset.subset_univ s) fun c _ hc => hf c hc).symm

lemma norm_extZ (μ : L2 s V) : ‖extZ s μ‖ = ‖μ‖ := by
  have h : ‖extZ s μ‖ ^ 2 = ‖μ‖ ^ 2 := by
    rw [norm_sq_L2, norm_sq_L2]
    rw [sum_extZ s _ fun c hc => by rw [extZ_out s μ hc, norm_zero]; ring]
    exact Finset.sum_congr rfl fun c _ => by rw [extZ_coe]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

lemma kerApply_compress (K : ι → ι → (V →L[ℂ] V)) (μ : L2 s V) (c : s) :
    (kerApply (compress s K) μ).ofLp c = (kerApply K (extZ s μ)).ofLp c := by
  rw [kerApply_apply, kerApply_apply]
  rw [sum_extZ s (fun c' => K c c' ((extZ s μ).ofLp c')) fun c' hc' => by rw [extZ_out s μ hc', map_zero]]
  exact Finset.sum_congr rfl fun c' _ => by rw [extZ_coe]; rfl

lemma conjKer_compress (θ : ℝ) (ρ : ι → ℝ) (K : ι → ι → (V →L[ℂ] V)) :
    conjKer θ (fun c : s => ρ c) (compress s K) = compress s (conjKer θ ρ K) := rfl

/-- The compression does not increase the norm. -/
lemma compress_opBound {K : ι → ι → (V →L[ℂ] V)} {M : ℝ} (hK : OpBound K M) :
    OpBound (compress s K) M := fun μ => by
  have h1 : ‖kerApply (compress s K) μ‖ ^ 2 ≤ ‖kerApply K (extZ s μ)‖ ^ 2 := by
    rw [norm_sq_L2, norm_sq_L2]
    simp only [kerApply_compress]
    rw [Finset.sum_coe_sort s (fun c => ‖(kerApply K (extZ s μ)).ofLp c‖ ^ 2)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _
  have h2 := hK (extZ s μ)
  rw [norm_extZ] at h2
  have h3 : ‖kerApply (compress s K) μ‖ ≤ ‖kerApply K (extZ s μ)‖ :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1
  exact h3.trans h2

/-- The compression keeps the coercivity `Re⟨μ, 𝒯₀μ⟩ ≥ γ‖μ‖²`. -/
lemma compress_coercive {T0 : ι → ι → (V →L[ℂ] V)} {γ : ℝ}
    (hcoer : ∀ μ : L2 ι V, γ * ‖μ‖ ^ 2 ≤ RCLike.re (inner ℂ μ (kerApply T0 μ))) (μ : L2 s V) :
    γ * ‖μ‖ ^ 2 ≤ RCLike.re (inner ℂ μ (kerApply (compress s T0) μ)) := by
  have h := hcoer (extZ s μ)
  rw [norm_extZ] at h
  have e : inner ℂ (extZ s μ) (kerApply T0 (extZ s μ)) = inner ℂ μ (kerApply (compress s T0) μ) := by
    rw [PiLp.inner_apply, PiLp.inner_apply]
    rw [sum_extZ s _ fun c hc => by rw [extZ_out s μ hc, inner_zero_left]]
    exact Finset.sum_congr rfl fun c _ => by rw [kerApply_compress, extZ_coe]
  rwa [e] at h

/-- **`lem:local-inverse`(ii)**: `F = 1_{S_□}(𝒯₀ + 𝒯₁)1_{S_□} - E` is invertible on the functions on `S_□`, and the
solution of `Fu = δ_{c'}w` has `‖u(c)‖ ≤ (2/γ)e^{-θd(c₋, c'₋)}‖w‖`. -/
theorem local_inverse_ii {B : Type*} [PseudoMetricSpace B] (fe : ι → B)
    {δ δ' κ γ θ0 K K' ε : ℝ} (hδ : 0 < δ) (hκ : 0 < κ) (hγ : 0 < γ) (hθ0 : 0 < θ0) (hθ0' : θ0 ≤ δ' / 2)
    (hK0 : 0 < K) (hε : 0 ≤ ε)
    (hK : ∀ c, ∑ c', Real.exp (-(δ / 4) * dist (fe c) (fe c')) ≤ K)
    (hK' : ∀ c, ∑ c', Real.exp (-(δ' / 2) * dist (fe c) (fe c')) ≤ K') (hsmall : K' * ε ≤ γ / 8)
    (T0 T1 : ι → ι → (V →L[ℂ] V))
    (ha : ∀ c c', ‖T0 c c'‖ ≤ κ * Real.exp (-δ * dist (fe c) (fe c')))
    (hcoer : ∀ μ : L2 ι V, γ * ‖μ‖ ^ 2 ≤ RCLike.re (inner ℂ μ (kerApply T0 μ)))
    (hc : ∀ y : B, ∀ θ, 0 ≤ θ → θ ≤ θ0 → OpBound (conjKer θ (fun c => dist (fe c) y) T1) (γ / 8))
    (E : s → s → (V →L[ℂ] V)) (hE : ∀ c c', ‖E c c'‖ ≤ ε * Real.exp (-δ' * dist (fe c) (fe c'))) :
    Function.Bijective (kerLin (compress s T0 + (compress s T1 - E))) ∧
    ∀ (c c' : s) (u : L2 s V) (w : V), kerApply (compress s T0 + (compress s T1 - E)) u = single c' w →
      ‖u.ofLp c‖ ≤ 2 / γ * Real.exp (-(min θ0 (min (δ / 2) (γ * δ / (6 * κ * K)))) *
        dist (fe c) (fe c')) * ‖w‖ := by
  have hsub : ∀ (r : ℝ) (c : s), ∑ c' : s, Real.exp (-r * dist (fe c) (fe c')) ≤
      ∑ c' : ι, Real.exp (-r * dist (fe (c : ι)) (fe c')) := fun r c => by
    rw [Finset.sum_coe_sort s (fun c' => Real.exp (-r * dist (fe (c : ι)) (fe c')))]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => (Real.exp_pos _).le
  have hK2 : ∀ c : s, ∑ c' : s, Real.exp (-(δ / 4) * dist (fe c) (fe c')) ≤ K := fun c => (hsub _ c).trans (hK c)
  have hco := compress_coercive s hcoer
  have ha2 : ∀ c c' : s, ‖compress s T0 c c'‖ ≤ κ * Real.exp (-δ * dist (fe c) (fe c')) := fun c c' => ha c c'
  have hcT : ∀ y : B, ∀ θ, 0 ≤ θ → θ ≤ θ0 →
      OpBound (conjKer θ (fun c : s => dist (fe c) y) (compress s T1 - E)) (γ / 4) := by
    intro y θ h0 h1
    rw [conjKer_sub]
    have hT1 : OpBound (conjKer θ (fun c : s => dist (fe c) y) (compress s T1)) (γ / 8) := by
      rw [conjKer_compress s θ (fun c => dist (fe c) y) T1]
      exact compress_opBound s (hc y θ h0 h1)
    have hE' : OpBound (conjKer θ (fun c : s => dist (fe c) y) E) (K' * ε) :=
      local_inverse_i (fun c : s => fe c) hε (fun c => (hsub _ c).trans (hK' c)) E hE y h0
        (h1.trans hθ0')
    have := hT1.sub hE'
    intro μ
    exact (this μ).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  exact kernel_inverse (fun c : s => fe c) hδ hκ hγ hθ0 hK0 hK2 (compress s T0) (compress s T1 - E) ha2 hco hcT

end CoreLean

end
