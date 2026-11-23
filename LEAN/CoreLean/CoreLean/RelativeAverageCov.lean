/-
`prop:relative-average`(ii) of BALABAN_CORE.tex (`d8bdc4ac1777`), the covariance, on the lattice.

For a gauge transformation `u` (or a complex one) with `‖Ad_{u(y)}X‖ ≤ 2‖X‖` at the sites concerned, the condition of
`lem:group-mean`, and exponents of norm at most `ϱ_m = 2^{-10}`:

* `moveC_gauge`: `(𝐔^u)_{Ad_uA} = (𝐔_A)^u`;
* `meanV_Ad`, `mean_conj`: the mean is covariant, `𝗆({u𝐖ᵢv}) = u𝗆({𝐖ᵢ})v`;
* `trans_gauge`: `𝐔^u(y, x) = u(y)𝐔(y, x)u(x)⁻¹`;
* `siteFactor_gauge`: `v_{𝐔^u}(Ad_uA)(y) = u(y)v_𝐔(A)(y)u(y)⁻¹`;
* `relAvg_gauge`: `𝓜_{𝐔^u}(Ad_uA)(c) = u(c₋)𝓜_𝐔(A)(c)u(c₋)⁻¹` (with `lem:average`(iii), `avgLogU_gauge`);
* `blockAvg_gauge`: `Q'(𝐔^u)Ad_u = Ad_uQ'(𝐔)`.
-/
import CoreLean.RelativeAverageLocal

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace RelativeAverage

open LatticePaths LatticeKappa RegularAverages BlockPaths AverageHolo MeanTransports GroupMean

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

variable {n : ℕ} [NeZero n]

/-- The `1`-form `Ad_uA`, `(Ad_uA)(b) = Ad_{u(b₋)}A(b)` on the positive bonds. -/
def AdF (u : Site n → GLN) (B : Fin 4 → Site n → Mat) : Fin 4 → Site n → Mat := fun μ z => Ad (u z) (B μ z)

lemma expU_Ad (u : GLN) (X : Mat) : expU (Ad u X) = u * expU X * u⁻¹ := (expU_conj u X).symm

/-- `(𝐔^u)_{Ad_uA} = (𝐔_A)^u`. -/
theorem moveC_gauge (V : Config N n) (u : Site n → GLN) (B : Fin 4 → Site n → Mat) :
    moveC (V.gauge u) (AdF u B) = (moveC V B).gauge u := by
  funext μ z
  simp only [moveC, Config.gauge, AdF, ← Ad_smul, expU_Ad]
  group

/-- The covariance of the solution of `eq:group-mean`. -/
theorem meanV_Ad {k : ℕ} (hk : 0 < k) (u : GLN) (hu : ∀ X : Mat, ‖Ad u X‖ ≤ 2 * ‖X‖) {Y : Fin k → Mat}
    (hY : ∀ i, ‖Y i‖ ≤ 1 / 1024) : meanV (fun i => Ad u (Y i)) = Ad u (meanV Y) := by
  have hY512 : ∀ i, ‖Y i‖ ≤ 1 / 512 := fun i => (hY i).trans (by norm_num)
  symm
  refine meanV_unique hk (fun i => (hu _).trans (by linarith [hY i])) ?_
    (solves_Ad u Y (meanV Y) (meanV_spec hk hY512).2)
  have := norm_meanV_le hk hY512 (1 / 1024) hY
  linarith [hu (meanV Y)]

/-- **The covariance of the mean**: `𝗆({u𝐖ᵢv}) = u𝗆({𝐖ᵢ})v`. -/
theorem mean_conj {k : ℕ} (hk : 0 < k) (u v : GLN) (hu : ∀ X : Mat, ‖Ad u X‖ ≤ 2 * ‖X‖) {Y : Fin k → Mat}
    (hY : ∀ i, ‖Y i‖ ≤ 1 / 1024) (W : GLN) :
    mean (fun i => Ad u (Y i)) (u * W * v) = u * mean Y W * v := by
  simp only [mean, meanV_Ad hk u hu hY, ← Ad_smul, expU_Ad]
  group

/-- The holonomies of the paths of `𝐆(y, x)` change by `u` at their ends. -/
lemma holG_gauge (V : Config N n) (u : Site n → GLN) (y : Site n) (h : ℕ) (x : Pts h) (Γ : Ords (offP h x)) :
    holG (V.gauge u) y h x Γ = u y * holG V y h x Γ * (u (ofs y (offP h x)))⁻¹ := by
  have hc := chain_endpt_stair y (offP h x) (ordG h x Γ) 0
  rw [ofs_zero, zero_add, offs_perm _ (ordG_perm h x Γ)] at hc
  rw [holG, holG, hol_gauge V u _ y hc.1, hc.2]

/-- The exponents of the transports are conjugated by `u(y)`. -/
lemma expsG_gauge (V : Config N n) (u : Site n → GLN) (y : Site n) (h : ℕ) (x : Pts h) :
    expsG (V.gauge u) y h x = fun i => Ad (u y) (expsG V y h x i) := by
  funext i
  have e : (holG (V.gauge u) y h x (enumG h x i) * (holG (V.gauge u) y h x (firstG h x))⁻¹ : GLN) =
      u y * (holG V y h x (enumG h x i) * (holG V y h x (firstG h x))⁻¹) * (u y)⁻¹ := by
    rw [holG_gauge, holG_gauge]; group
  simp only [expsG, e]
  rw [show ((u y * (holG V y h x (enumG h x i) * (holG V y h x (firstG h x))⁻¹) * (u y)⁻¹ : GLN) : Mat) =
      Ad (u y) ((holG V y h x (enumG h x i) * (holG V y h x (firstG h x))⁻¹ : GLN) : Mat) by
    simp only [Ad, Units.val_mul], LogM_conj, Ad_smul]

/-- **The covariance of the transports**: `𝐔^u(y, x) = u(y)𝐔(y, x)u(x)⁻¹`. -/
theorem trans_gauge (V : Config N n) (u : Site n → GLN) (y : Site n) (h : ℕ) (x : Pts h)
    (hu : ∀ X : Mat, ‖Ad (u y) X‖ ≤ 2 * ‖X‖) (hY : ∀ i, ‖expsG V y h x i‖ ≤ 1 / 1024) :
    trans (V.gauge u) y h x = u y * trans V y h x * (u (ofs y (offP h x)))⁻¹ := by
  rw [trans, expsG_gauge, holG_gauge, mean_conj (card_ords_pos _) _ _ hu hY, trans]

/-- **The covariance of the site factors**: `v_{𝐔^u}(Ad_uA)(y) = u(y)v_𝐔(A)(y)u(y)⁻¹`. -/
theorem siteFactor_gauge (V : Config N n) (u : Site n → GLN) (B : Fin 4 → Site n → Mat) (y : Site n) (h : ℕ)
    (hu : ∀ X : Mat, ‖Ad (u y) X‖ ≤ 2 * ‖X‖) (hY : ∀ x i, ‖expsG V y h x i‖ ≤ 1 / 1024)
    (hYA : ∀ x i, ‖expsG (moveC V B) y h x i‖ ≤ 1 / 1024) :
    siteFactor (V.gauge u) (AdF u B) y h = u y * siteFactor V B y h * (u y)⁻¹ := by
  have e : ∀ x : Pts h, LogM ((trans (moveC (V.gauge u) (AdF u B)) y h x * (trans (V.gauge u) y h x)⁻¹ : GLN) :
      Mat) = Ad (u y) (LogM ((trans (moveC V B) y h x * (trans V y h x)⁻¹ : GLN) : Mat)) := fun x => by
    rw [moveC_gauge, trans_gauge _ _ _ _ _ hu (hYA x), trans_gauge _ _ _ _ _ hu (hY x)]
    rw [show (u y * trans (moveC V B) y h x * (u (ofs y (offP h x)))⁻¹ *
        (u y * trans V y h x * (u (ofs y (offP h x)))⁻¹)⁻¹ : GLN) =
        u y * (trans (moveC V B) y h x * (trans V y h x)⁻¹) * (u y)⁻¹ by group]
    rw [show ((u y * (trans (moveC V B) y h x * (trans V y h x)⁻¹) * (u y)⁻¹ : GLN) : Mat) =
        Ad (u y) ((trans (moveC V B) y h x * (trans V y h x)⁻¹ : GLN) : Mat) by
      simp only [Ad, Units.val_mul], LogM_conj]
  simp only [siteFactor, e, ← Ad_sum, ← Ad_smul, expU_Ad]

/-- The average of the family `𝐆` is covariant (`lem:average`(iii), `avgLogU_gauge`). -/
lemma avgM_gauge (V : Config N n) (u : Site n → GLN) (y : Site n) (μ : Fin 4) (h : ℕ) :
    avgM (V.gauge u) y μ h = u y * avgM V y μ h * (u (cPlus y μ h))⁻¹ :=
  avgLogU_gauge V u y μ (2 * h + 1) (offP h) (ordG h) (ordG_perm h)

/-- **The covariance of the relative average**: `𝓜_{𝐔^u}(Ad_uA)(c) = u(c₋)𝓜_𝐔(A)(c)u(c₋)⁻¹`. -/
theorem relAvg_gauge (V : Config N n) (u : Site n → GLN) (B : Fin 4 → Site n → Mat) (y : Site n) (μ : Fin 4)
    (h : ℕ) (hu : ∀ X : Mat, ‖Ad (u y) X‖ ≤ 2 * ‖X‖) (hu' : ∀ X : Mat, ‖Ad (u (cPlus y μ h)) X‖ ≤ 2 * ‖X‖)
    (hY : ∀ x i, ‖expsG V y h x i‖ ≤ 1 / 1024) (hYA : ∀ x i, ‖expsG (moveC V B) y h x i‖ ≤ 1 / 1024)
    (hY' : ∀ x i, ‖expsG V (cPlus y μ h) h x i‖ ≤ 1 / 1024)
    (hYA' : ∀ x i, ‖expsG (moveC V B) (cPlus y μ h) h x i‖ ≤ 1 / 1024) :
    relAvg (V.gauge u) (AdF u B) y μ h = u y * relAvg V B y μ h * (u y)⁻¹ := by
  rw [relAvg, siteFactor_gauge V u B y h hu hY hYA, siteFactor_gauge V u B _ h hu' hY' hYA', moveC_gauge,
    avgM_gauge, avgM_gauge, relAvg]
  group

/-- **The covariance of the block average**: `Q'(𝐔^u)Ad_uλ = Ad_uQ'(𝐔)λ`. -/
theorem blockAvg_gauge (V : Config N n) (u : Site n → GLN) (lam : Site n → Mat) (y : Site n) (h : ℕ)
    (hu : ∀ X : Mat, ‖Ad (u y) X‖ ≤ 2 * ‖X‖) (hY : ∀ x i, ‖expsG V y h x i‖ ≤ 1 / 1024) :
    blockAvg (V.gauge u) (fun z => Ad (u z) (lam z)) y h = Ad (u y) (blockAvg V lam y h) := by
  simp only [blockAvg, trans_gauge V u y h _ hu (hY _), Ad_mul, Ad_inv_Ad, Ad_smul, Ad_sum]

end RelativeAverage
end CoreLean

end
