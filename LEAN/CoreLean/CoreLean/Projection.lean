/-
The orthogonal projection `π` of `M_N(ℂ)` onto `𝔤^c` with respect to `⟨X, Y⟩ = tr X^* Y`
(`def:group`(ii)–(iii)) and `lem:norms`(iii)–(iv) of BALABAN_CORE.tex.

The scalar product is carried by the flattening `flat : M_N(ℂ) ≃ ℂ^{N×N}` onto
`EuclideanSpace ℂ (Fin N × Fin N)`, whose scalar product is `Tr X^* Y = N tr X^* Y` (`inner_flat`);
a positive multiple of the scalar product has the same orthogonal projections, and
`‖flat X‖ = √N |X|` (`norm_flat`).
-/
import CoreLean.Algebra
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

open Matrix Complex

namespace CoreLean

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-- The flattening `M_N(ℂ) ≃ ℂ^{N×N}`. -/
noncomputable def flat : Mat ≃ₗ[ℂ] EuclideanSpace ℂ (Fin N × Fin N) where
  toFun X := WithLp.toLp 2 fun p => X p.1 p.2
  invFun v := Matrix.of fun i j => v.ofLp (i, j)
  map_add' X Y := by ext p; simp
  map_smul' c X := by ext p; simp
  left_inv X := by ext i j; simp
  right_inv v := by ext p; simp

/-- The scalar product of `ℂ^{N×N}` is `Tr X^* Y`. -/
lemma inner_flat (X Y : Mat) : (inner ℂ (flat X) (flat Y) : ℂ) = (Xᴴ * Y).trace := by
  simp only [flat, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, PiLp.inner_apply,
    WithLp.ofLp_toLp, RCLike.inner_apply, Fintype.sum_prod_type, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [mul_comm]

lemma inner_flat_ntr (X Y : Mat) : (inner ℂ (flat X) (flat Y) : ℂ) = N * ntr (Xᴴ * Y) := by
  rw [inner_flat]
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp [Matrix.trace]
  · rw [ntr, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast h.ne'), one_mul]

/-- `‖flat X‖ = √N |X|`. -/
lemma norm_flat (X : Mat) : ‖flat X‖ = Real.sqrt N * hs X := by
  have h := @norm_sq_eq_re_inner ℂ _ _ _ _ (flat X)
  rw [inner_flat_ntr] at h
  have h2 : RCLike.re ((N : ℂ) * ntr (Xᴴ * X)) = N * hs2 X := by
    simp [hs2, RCLike.re_to_complex]
  rw [h2] at h
  rw [hs, ← Real.sqrt_mul (Nat.cast_nonneg N), ← h, Real.sqrt_sq (norm_nonneg _)]

variable {G : GaugeGroup N}

/-- `𝔤^c` in `ℂ^{N×N}`. -/
noncomputable def lieCE (hG : G.LieInput) : Submodule ℂ (EuclideanSpace ℂ (Fin N × Fin N)) :=
  (GaugeGroup.lieCSubmodule hG).map
    ((flat (N := N) : Mat ≃ₗ[ℂ] EuclideanSpace ℂ (Fin N × Fin N)) :
      Mat →ₗ[ℂ] EuclideanSpace ℂ (Fin N × Fin N))

lemma mem_lieCE (hG : G.LieInput) {X : Mat} : flat X ∈ lieCE hG ↔ X ∈ G.lieC := by
  rw [lieCE, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply,
    GaugeGroup.mem_lieCSubmodule]

lemma mem_lieCE' (hG : G.LieInput) {v : EuclideanSpace ℂ (Fin N × Fin N)} :
    v ∈ lieCE hG ↔ flat.symm v ∈ G.lieC := by
  rw [← mem_lieCE hG, LinearEquiv.apply_symm_apply]

/-- The orthogonal projection `π` onto `𝔤^c` (`def:group`(iii)). -/
noncomputable def piProj (hG : G.LieInput) (X : Mat) : Mat :=
  flat.symm ((lieCE hG).starProjection (flat X))

lemma flat_proj (hG : G.LieInput) (X : Mat) :
    flat (piProj hG X) = (lieCE hG).starProjection (flat X) := LinearEquiv.apply_symm_apply _ _

lemma proj_mem (hG : G.LieInput) (X : Mat) : piProj hG X ∈ G.lieC :=
  (mem_lieCE' hG).1 ((lieCE hG).starProjection_apply_mem (flat X))

/-- `X - πX` is orthogonal to `𝔤^c`: `tr Z^*(X - πX) = 0` for `Z ∈ 𝔤^c`. -/
lemma proj_orth [NeZero N] (hG : G.LieInput) (X : Mat) {Z : Mat} (hZ : Z ∈ G.lieC) :
    ntr (Zᴴ * (X - piProj hG X)) = 0 := by
  have h := (lieCE hG).starProjection_inner_eq_zero (flat X) (flat Z) ((mem_lieCE hG).2 hZ)
  rw [← inner_conj_symm, map_eq_zero, ← flat_proj, ← map_sub, inner_flat_ntr] at h
  exact (mul_eq_zero.1 h).resolve_left (by exact_mod_cast NeZero.ne N)

/-- The characterisation of `π`: the point of `𝔤^c` with `X - Y ⊥ 𝔤^c`. -/
lemma proj_eq (hG : G.LieInput) {X Y : Mat} (hY : Y ∈ G.lieC)
    (h : ∀ Z ∈ G.lieC, ntr (Zᴴ * (X - Y)) = 0) : piProj hG X = Y := by
  have : (lieCE hG).starProjection (flat X) = flat Y := by
    refine (lieCE hG).eq_starProjection_of_mem_of_inner_eq_zero ((mem_lieCE hG).2 hY)
      fun w hw => ?_
    rw [← inner_conj_symm, map_eq_zero, ← LinearEquiv.apply_symm_apply flat w, ← map_sub,
      inner_flat_ntr, h _ ((mem_lieCE' hG).1 hw), mul_zero]
  rw [piProj, this, LinearEquiv.symm_apply_apply]

/-- `lem:norms`(iv): `π` is complex linear. -/
theorem proj_add (hG : G.LieInput) (X Y : Mat) : piProj hG (X + Y) = piProj hG X + piProj hG Y := by
  simp [piProj, map_add]

theorem proj_smul (hG : G.LieInput) (c : ℂ) (X : Mat) : piProj hG (c • X) = c • piProj hG X := by
  simp [piProj, map_smul]

/-- `lem:norms`(iv): `|πX| ≤ |X|`. -/
theorem hs_proj_le [NeZero N] (hG : G.LieInput) (X : Mat) : hs (piProj hG X) ≤ hs X := by
  have h := (lieCE hG).norm_starProjection_apply_le (flat X)
  rw [← flat_proj, norm_flat, norm_flat] at h
  have hN : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast NeZero.pos N)
  exact le_of_mul_le_mul_left h hN

open scoped Matrix.Norms.L2Operator in
/-- `lem:norms`(iv): `‖πX‖ ≤ √N ‖X‖`. -/
theorem opNorm_proj_le [NeZero N] (hG : G.LieInput) (X : Mat) :
    ‖piProj hG X‖ ≤ Real.sqrt N * ‖X‖ :=
  (opNorm_le_sqrt_mul_hs _).trans (mul_le_mul_of_nonneg_left
    ((hs_proj_le hG X).trans (hs_le_opNorm (NeZero.pos N) X)) (Real.sqrt_nonneg _))

/-- `tr((A B)^*) = conj tr(A B)`, and `tr AB = tr BA`. -/
lemma ntr_conjTranspose (X : Mat) : ntr Xᴴ = starRingEnd ℂ (ntr X) := by
  simp [ntr, Matrix.trace_conjTranspose, map_mul, map_inv₀]

/-- `X ⊥ 𝔤^c` if and only if `tr Z X = 0` for all `Z ∈ 𝔤^c`, since `𝔤^c` is closed under `^*`. -/
lemma orth_iff (G : GaugeGroup N) {W : Mat} :
    (∀ Z ∈ G.lieC, ntr (Zᴴ * W) = 0) ↔ (∀ Z ∈ G.lieC, ntr (Z * W) = 0) := by
  constructor
  · intro h Z hZ
    simpa using h Zᴴ (GaugeGroup.conjTranspose_mem_lieC hZ)
  · intro h Z hZ
    exact h Zᴴ (GaugeGroup.conjTranspose_mem_lieC hZ)

/-- `lem:norms`(iv): `π(X^*) = (πX)^*`. -/
theorem proj_conjTranspose [NeZero N] (hG : G.LieInput) (X : Mat) :
    piProj hG Xᴴ = (piProj hG X)ᴴ := by
  refine proj_eq hG (GaugeGroup.conjTranspose_mem_lieC (proj_mem hG X)) fun Z hZ => ?_
  -- `tr Z^*(X - πX)^* = conj tr((X - πX) Z) = conj tr(Z(X - πX))`
  rw [← Matrix.conjTranspose_sub, ← Matrix.conjTranspose_mul, ntr_conjTranspose]
  rw [show ntr ((X - piProj hG X) * Z) = ntr (Z * (X - piProj hG X)) by
    unfold ntr; rw [Matrix.trace_mul_comm]]
  rw [(orth_iff G).mp (fun Z hZ => proj_orth hG X hZ) Z hZ, map_zero]

/-- `lem:norms`(iii): for `U ∈ G^c`, `Ad_U` commutes with `π`. -/
theorem proj_Ad [NeZero N] (hG : G.LieInput) {U : GLN} (hU : U ∈ G.complexified) (X : Mat) :
    piProj hG (Ad U X) = Ad U (piProj hG X) := by
  refine proj_eq hG (GaugeGroup.Ad_mem_lieC hG hU (proj_mem hG X)) ?_
  refine (orth_iff G).mpr fun Z hZ => ?_
  -- `tr Z Ad_U W = tr (Ad_{U⁻¹} Z) W = 0` with `W = X - πX ⊥ 𝔤^c`
  have hW := (orth_iff G).mp (fun Z hZ => proj_orth hG X hZ)
  rw [← Ad_sub]
  have hcyc : ntr (Z * Ad U (X - piProj hG X)) = ntr (Ad U⁻¹ Z * (X - piProj hG X)) := by
    unfold ntr
    rw [Matrix.trace_mul_comm, trace_Ad_mul, Matrix.trace_mul_comm]
  rw [hcyc]
  exact hW _ (GaugeGroup.Ad_mem_lieC hG (G.complexified.inv_mem hU) hZ)

end CoreLean
