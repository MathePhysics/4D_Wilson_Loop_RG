import Mathlib

/-!
# Smoothness of the superposition operator on a space of continuous curves

For a compact space `K` and a `C^n` map `f : E → F` between real normed spaces, post-composition
`γ ↦ f ∘ γ` is a `C^n` map `C(K, E) → C(K, F)` (the "omega lemma").  This is the one analytic
ingredient missing from mathlib for smooth dependence of ODE solutions on parameters by the
Banach-space implicit function theorem.
-/

noncomputable section

open scoped Topology
open Set Metric Filter Asymptotics

universe u

namespace LieGroupExponential
namespace OmegaLemma

section UniformNearCompact

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

/-- A continuous map is uniformly continuous *at* a compact set: the modulus is uniform over base
points in the compact set, while the second point is arbitrary. -/
theorem exists_forall_dist_lt_of_isCompact {g : X → Y} (hg : Continuous g) {S : Set X}
    (hS : IsCompact S) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ S, ∀ y, dist y x < δ → dist (g y) (g x) < ε := by
  let T : Set (X × X) := {p | dist (g p.2) (g p.1) < ε}
  have hT : IsOpen T :=
    isOpen_lt ((hg.comp continuous_snd).dist (hg.comp continuous_fst)) continuous_const
  have hD : IsCompact ((fun x => (x, x)) '' S) := hS.image (continuous_id.prodMk continuous_id)
  have hDT : (fun x => (x, x)) '' S ⊆ T := by
    rintro _ ⟨x, -, rfl⟩
    simpa [T] using hε
  obtain ⟨δ, hδ, hsub⟩ := hD.exists_thickening_subset_open hT hDT
  refine ⟨δ, hδ, fun x hx y hy => ?_⟩
  have hmem : (x, y) ∈ thickening δ ((fun x => (x, x)) '' S) := by
    rw [mem_thickening_iff]
    refine ⟨(x, x), ⟨x, hx, rfl⟩, ?_⟩
    rw [Prod.dist_eq]
    simp [hy]
  exact hsub hmem

end UniformNearCompact

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Apply

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Pointwise application of a continuous family of operators to a continuous curve, as a
bilinear map. -/
def pointwiseApplyLM : C(K, E →L[ℝ] F) →ₗ[ℝ] C(K, E) →ₗ[ℝ] C(K, F) where
  toFun A :=
    { toFun := fun δ => ⟨fun t => A t (δ t), A.continuous.clm_apply δ.continuous⟩
      map_add' := fun δ δ' => by ext t; simp
      map_smul' := fun c δ => by ext t; simp }
  map_add' A A' := by ext δ t; simp
  map_smul' c A := by ext δ t; simp

theorem norm_pointwiseApplyLM_le (A : C(K, E →L[ℝ] F)) (δ : C(K, E)) :
    ‖pointwiseApplyLM A δ‖ ≤ 1 * ‖A‖ * ‖δ‖ := by
  rw [one_mul, ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg δ))]
  intro t
  exact ((A t).le_opNorm (δ t)).trans
    (mul_le_mul (A.norm_coe_le_norm t) (δ.norm_coe_le_norm t) (norm_nonneg _) (norm_nonneg _))

/-- Pointwise application of a continuous family of operators to a continuous curve, as a
continuous bilinear map of norm at most one. -/
def pointwiseApply : C(K, E →L[ℝ] F) →L[ℝ] C(K, E) →L[ℝ] C(K, F) :=
  LinearMap.mkContinuous₂ (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜₃ := ℝ) (E := C(K, E →L[ℝ] F)) (F := C(K, E))
    (G := C(K, F)) (σ₁₃ := RingHom.id ℝ) (σ₂₃ := RingHom.id ℝ) pointwiseApplyLM 1
    norm_pointwiseApplyLM_le

@[simp]
theorem pointwiseApply_apply (A : C(K, E →L[ℝ] F)) (δ : C(K, E)) (t : K) :
    pointwiseApply A δ t = A t (δ t) := by
  rw [pointwiseApply, LinearMap.mkContinuous₂_apply]
  rfl

/-- The superposition (post-composition) operator of a continuous map. -/
def superposition (f : E → F) (hf : Continuous f) (γ : C(K, E)) : C(K, F) :=
  ⟨f ∘ γ, hf.comp γ.continuous⟩

omit [CompactSpace K] [NormedSpace ℝ E] [NormedSpace ℝ F] in
@[simp]
theorem superposition_apply (f : E → F) (hf : Continuous f) (γ : C(K, E)) (t : K) :
    superposition f hf γ t = f (γ t) := rfl

omit [CompactSpace K] [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem continuous_superposition (f : E → F) (hf : Continuous f) :
    Continuous (superposition (K := K) f hf) :=
  ContinuousMap.continuous_postcomp ⟨f, hf⟩

/-- The `C¹` step of the omega lemma: the superposition operator of a `C¹` map is differentiable,
with derivative the pointwise application of `Df ∘ γ`. -/
theorem hasFDerivAt_superposition {f : E → F} (hf : ContDiff ℝ 1 f) (γ : C(K, E)) :
    HasFDerivAt (superposition (K := K) f hf.continuous)
      (pointwiseApply (superposition (fderiv ℝ f) (hf.continuous_fderiv one_ne_zero) γ)) γ := by -- totalisation-audit: allow the map is C^1 at this point, so fderiv is its genuine derivative
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hunif⟩ := exists_forall_dist_lt_of_isCompact (hf.continuous_fderiv one_ne_zero)
    (isCompact_range γ.continuous) hc
  filter_upwards [Metric.ball_mem_nhds (0 : C(K, E)) hδ] with h hh
  rw [mem_ball_zero_iff] at hh
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun t => ?_
  have hht : ‖h t‖ < δ := (h.norm_coe_le_norm t).trans_lt hh
  have hbound : ∀ z ∈ ball (γ t) δ, ‖fderiv ℝ f z - fderiv ℝ f (γ t)‖ ≤ c := fun z hz => by -- totalisation-audit: allow the map is C^1 at this point, so fderiv is its genuine derivative
    rw [← dist_eq_norm]
    exact (hunif (γ t) (mem_range_self t) z hz).le
  have hmv := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (f := f) (f' := fderiv ℝ f) (φ := fderiv ℝ f (γ t)) (s := ball (γ t) δ) -- totalisation-audit: allow the map is C^1 at this point, so fderiv is its genuine derivative
    (fun z _ => ((hf.differentiable one_ne_zero) z).hasFDerivAt.hasFDerivWithinAt) hbound
    (convex_ball _ _) (mem_ball_self hδ) (show γ t + h t ∈ ball (γ t) δ by simpa using hht)
  have hle : c * ‖γ t + h t - γ t‖ ≤ c * ‖h‖ := by
    rw [add_sub_cancel_left]
    exact mul_le_mul_of_nonneg_left (h.norm_coe_le_norm t) hc.le
  simpa using hmv.trans hle

end Apply

/-- The omega lemma: the superposition operator of a `C^n` map is `C^n`.  The spaces are kept in
one universe so that the induction can pass from `F` to `E →L[ℝ] F`. -/
theorem contDiff_superposition :
    ∀ (n : ℕ) {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
      (hf : ContDiff ℝ n f), ContDiff ℝ n (superposition (K := K) f hf.continuous)
  | 0, _, _, _, f, hf => contDiff_zero.2 (continuous_superposition f hf.continuous)
  | n + 1, F, _, _, f, hf => by
      have h1 : ContDiff ℝ 1 f := hf.of_le (by norm_cast; omega)
      have hD : ContDiff ℝ n (fderiv ℝ f) := hf.fderiv_right le_rfl -- totalisation-audit: allow the map is C^1 at this point, so fderiv is its genuine derivative
      refine contDiff_succ_iff_hasFDerivAt.2
        ⟨fun γ => pointwiseApply (superposition (fderiv ℝ f) hD.continuous γ), ?_, -- totalisation-audit: allow the map is C^1 at this point, so fderiv is its genuine derivative
          fun γ => hasFDerivAt_superposition h1 γ⟩
      exact (pointwiseApply (K := K) (E := E) (F := F)).contDiff.comp
        (contDiff_superposition n hD)

end OmegaLemma
end LieGroupExponential
