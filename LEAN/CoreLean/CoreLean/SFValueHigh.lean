/-
`prop:sf-bounds` of BALABAN_CORE.tex (`4252790331fd`), the step "Values in the layers `j ≥ 2`", first part: the local
equation `(H2)` on the fine lattice (`a₀ = 1`) gives the hypotheses of `lem:sf-local` on the boxes about a site of a
scale `j ≥ 2`, and `lem:sf-local`(i) bounds the values on `Q_4`.

* `LocalEqn`: `(H2)` at the sites of the Dirichlet domain, `Δ_𝐔u = f + D^*_𝐔g + 𝒵u + 𝒩u + 𝓕u` on the members, with the
  values `𝒵u`, `𝒩u`, `𝓕u` of the maps at `u` and the coefficients `Z_e(z)` of `𝒵` (`hZrep`).
* `sfData`: the data of `lem:sf-local` in the coordinates of the layer: `ũ`, `a²(f + 𝓕u)`, `ag_μ`, `a²Z_e`, `a²𝒩u`.
* `sfHyp_of`: the hypotheses `SFHyp` on the box about `x`, `j(x) ≥ 2`, from `(H2)`, the bounds of the field
  (`RegField`), `RM ≥ 8L²`, `Ω₁ ⊂ Ω_D`, `a²Σ_e‖Z_e‖ ≤ ¼` and the bound of `𝒩` of `lem:sf-local` on the box, and bounds
  `Fb`, `Gb` of `|f + 𝓕u|`, `|g_μ|` on `Q_{8+2L}`.
* `value_high`: `|u(z)| ≤ K_sf(a⁻²‖u‖_{2,Q_{8+2L}} + a²Fb + aGb)` for `z ∈ Q_4` (`lem:sf-local`(i)).
-/
import CoreLean.SFFarTerm

open Finset Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFBox SFBox.SeqDomBox SFLocal LocalLaplacian InteriorSchauder

variable (S : SeqDom) {N m : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "NF" => SequenceAverages.N0 S
local notation "RMS" => ((S.R * S.L ^ S.mM : ℕ) : ℝ)
set_option quotPrecheck false in
local notation "jj" => (S.toDomSeq).sc

/-- **`(H2)`**: the local equation at the sites of the Dirichlet domain, with the coefficients of `𝒵`. -/
structure LocalEqn (X : Fin 4 → Site NF → Mat) (ΩD : Set (Site NF)) (u f : Fin m → Site NF → Mat)
    (g : Fin m → Fin 4 → Site NF → Mat) (Zu Nu Fu : Fin m → Site NF → Mat)
    (Zc : Site NF → (Fin 4 → ℤ) → (VS N m →L[ℝ] VS N m)) : Prop where
  eqn : ∀ x ∈ ΩD, ∀ k, Lap 1 (cfgX X) (u k) x = f k x + Ds1 1 (cfgX X) (g k) x + Zu k x + Nu k x + Fu k x
  hZrep : ∀ z, (vecOf fun k => Zu k z) = ∑ e ∈ Eoff, Zc z e (vecOf fun k => u k (z + castS e))

lemma castS_add {n : ℕ} [NeZero n] (z e : Fin 4 → ℤ) : castS (n := n) (z + e) = castS z + castS e := by
  funext ν; simp [castS]

/-- `‖ũ(z)‖ = √N|u(z mod N₀)|`. -/
lemma norm_liftM (u : Fin m → Site NF → Mat) (z : Fin 4 → ℤ) :
    ‖SFBox.liftM (N := N) u z‖ = Real.sqrt N * Real.sqrt (nsq fun k => u k (castS z)) := by
  rw [← Real.sqrt_sq (norm_nonneg _), norm_liftM_sq, Real.sqrt_mul (Nat.cast_nonneg _)]
  rfl

/-- The data of `lem:sf-local` in the coordinates of the layer of the scale `j`. -/
def sfData (j : ℕ) (u f : Fin m → Site NF → Mat) (g : Fin m → Fin 4 → Site NF → Mat) (Nu Fu : Fin m → Site NF → Mat)
    (Zc : Site NF → (Fin 4 → ℤ) → (VS N m →L[ℝ] VS N m)) : SFData N m where
  u := SFBox.liftM u
  f := SFBox.liftM fun k x => (((S.L : ℝ) ^ j) ^ 2 : ℝ) • (f k x + Fu k x)
  g μ := SFBox.liftM fun k x => (((S.L : ℝ) ^ j : ℝ) : ℂ) • g k μ x
  Z z e := (((S.L : ℝ) ^ j) ^ 2 : ℝ) • Zc (castS z) e
  Nu := SFBox.liftM fun k x => (((S.L : ℝ) ^ j) ^ 2 : ℝ) • Nu k x

lemma vecOf_rsmul' (c : ℝ) (X : Fin m → Mat) : vecOf (fun k => c • X k) = c • vecOf (N := N) X := by
  ext p; simp [vecOf]

/-- **The hypotheses of `lem:sf-local` on the box about a site of a scale `j ≥ 2`.** -/
theorem sfHyp_of [NeZero N] {X : Fin 4 → Site NF → Mat} {α₁ : ℝ} (hX : RegField S X α₁) (hα0 : 0 ≤ α₁)
    (hα : 64 * (S.L : ℝ) ^ 2 * α₁ ≤ 1) (hRM : 8 * (S.L : ℝ) ^ 2 ≤ RMS) {ΩD : Set (Site NF)}
    (hD : ∀ x, S.ef x ∈ S.Ω 1 → x ∈ ΩD) {u f : Fin m → Site NF → Mat} {g : Fin m → Fin 4 → Site NF → Mat}
    {Zu Nu Fu : Fin m → Site NF → Mat} {Zc : Site NF → (Fin 4 → ℤ) → (VS N m →L[ℝ] VS N m)}
    (H : LocalEqn S X ΩD u f g Zu Nu Fu Zc) {x : Site NF} (hj : 2 ≤ jj x) {CN Fb Gb : ℝ} (hCN : 0 ≤ CN)
    (hZs : ∀ z, InQr ((S.L : ℝ) ^ jj x)⁻¹ (xbar x) 8 z →
      ((S.L : ℝ) ^ jj x) ^ 2 * ∑ e ∈ Eoff, ‖Zc (castS z) e‖ ≤ 1 / 4)
    (hN1 : ∀ z, InQr ((S.L : ℝ) ^ jj x)⁻¹ (xbar x) 8 z →
      ‖(sfData S (jj x) u f g Nu Fu Zc).Nu z‖ ≤
        CN * pn ((S.L : ℝ) ^ jj x)⁻¹ (QF ((S.L : ℝ) ^ jj x)⁻¹ (xbar x) (8 + 2 * S.L)) 2 (fun z => ‖SFBox.liftM (N := N) u z‖))
    (hFb : ∀ z, InQr ((S.L : ℝ) ^ jj x)⁻¹ (xbar x) (8 + 2 * S.L) z →
      Real.sqrt (nsq fun k => f k (castS z) + Fu k (castS z)) ≤ Fb)
    (hGb : ∀ μ z, InQr ((S.L : ℝ) ^ jj x)⁻¹ (xbar x) (8 + 2 * S.L) z →
      Real.sqrt (nsq fun k => g k μ (castS z)) ≤ Gb) :
    SFHyp ((S.L : ℝ) ^ jj x)⁻¹ (xbar x) (Atil ((S.L : ℝ) ^ jj x) X) S.L α₁ (sfData S (jj x) u f g Nu Fu Zc) CN
      (Real.sqrt N * ((S.L : ℝ) ^ jj x) ^ 2 * Fb) (Real.sqrt N * (S.L : ℝ) ^ jj x * Gb) := by
  set j := jj x
  set c : ℝ := (S.L : ℝ) ^ j
  have hL : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  have hc : 0 < c := by positivity
  have hcne : c ≠ 0 := hc.ne'
  have hj1 : 1 ≤ j := by omega
  refine ⟨fieldHyp_of S hX hα0 hα hRM x hj1, ?_, ?_, hCN, ?_, ?_, hN1⟩
  · -- the equation
    intro z hz
    have hL3 : (3 : ℝ) ≤ S.L := by exact_mod_cast S.three_le_L
    have hzΩ : castS (n := NF) z ∈ ΩD :=
      hD _ (S.Ω_anti (show 1 ≤ j - 1 by omega) (box_mem_Ω S hRM x (by linarith) hz))
    simp only [sfData]
    rw [covLapV_liftM hcne, sum_DbwV_liftM hcne]
    have hloc : locApp (fun z e => (c ^ 2 : ℝ) • Zc (castS z) e) (SFBox.liftM (N := N) u) z =
        SFBox.liftM (fun k x => ((c ^ 2 : ℝ) : ℂ) • Zu k x) z := by
      unfold locApp
      simp only [ContinuousLinearMap.smul_apply, SFBox.liftM, castS_add]
      rw [← smul_sum, ← H.hZrep, ← vecOf_rsmulM]
    rw [hloc]
    have hv : ∀ (Y : Fin m → Mat) (p : Fin m × Fin N × Fin N), (vecOf (N := N) Y) p = Y p.1 p.2.1 p.2.2 :=
      fun Y p => rfl
    ext p
    simp only [SFBox.liftM, PiLp.add_apply, hv]
    rw [H.eqn _ hzΩ p.1]
    simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, Complex.real_smul, c]
    push_cast
    ring
  · intro z hz
    have e : ∑ e ∈ Eoff, ‖(sfData S j u f g Nu Fu Zc).Z z e‖ = c ^ 2 * ∑ e ∈ Eoff, ‖Zc (castS z) e‖ := by
      rw [mul_sum]; refine sum_congr rfl fun e _ => ?_
      show ‖(c ^ 2 : ℝ) • Zc (castS z) e‖ = _
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [e]; exact hZs z hz
  · intro z hz
    simp only [sfData]
    rw [show (SFBox.liftM (fun k x => (c ^ 2 : ℝ) • (f k x + Fu k x)) z : VS N m) =
        (c ^ 2 : ℝ) • SFBox.liftM (fun k x => f k x + Fu k x) z by simp only [SFBox.liftM]; rw [vecOf_rsmul'],
      norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), norm_liftM]
    have := hFb z hz
    have h0 : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
    calc c ^ 2 * (Real.sqrt N * Real.sqrt (nsq fun k => f k (castS z) + Fu k (castS z)))
        ≤ c ^ 2 * (Real.sqrt N * Fb) := by gcongr
      _ = Real.sqrt N * c ^ 2 * Fb := by ring
  · intro μ z hz
    simp only [sfData]
    rw [show (SFBox.liftM (fun k x => ((c : ℝ) : ℂ) • g k μ x) z : VS N m) = c • SFBox.liftM (fun k x => g k μ x) z by
        simp only [SFBox.liftM]; rw [vecOf_rsmulM],
      norm_smul, Real.norm_eq_abs, abs_of_pos hc, norm_liftM]
    have := hGb μ z hz
    have h0 : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
    calc c * (Real.sqrt N * Real.sqrt (nsq fun k => g k μ (castS z)))
        ≤ c * (Real.sqrt N * Gb) := by gcongr
      _ = Real.sqrt N * c * Gb := by ring

/-- The `L²`-norm of the box of the layer in the fine units: `‖ũ‖_{2,Q} = √N a⁻²(Σ_{n ∈ Q}|u(n)|²)^{1/2}`. -/
lemma pn_liftM (j : ℕ) (T : Finset (Fin 4 → ℤ)) (u : Fin m → Site NF → Mat) :
    pn ((S.L : ℝ) ^ j)⁻¹ T 2 (fun z => ‖SFBox.liftM (N := N) u z‖) =
      Real.sqrt N * ((S.L : ℝ) ^ j)⁻¹ ^ 2 * Real.sqrt (∑ z ∈ T, nsq fun k => u k (castS z)) := by
  unfold pn
  have hL : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  have e : ∀ z, (((S.L : ℝ) ^ j)⁻¹) ^ 4 * ‖SFBox.liftM (N := N) u z‖ ^ (2 : ℝ) =
      (Real.sqrt N * ((S.L : ℝ) ^ j)⁻¹ ^ 2) ^ 2 * nsq fun k => u k (castS z) := by
    intro z
    rw [Real.rpow_two, norm_liftM_sq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp only [nsq]; ring
  simp only [e, ← mul_sum]
  rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (pow_two_nonneg _), Real.sqrt_sq (by positivity)]

/-- **The values on `Q_4` about a site of a scale `j ≥ 2`** (`lem:sf-local`(i)):
`|u(z)| ≤ K_sf(a⁻²(Σ_{n ∈ Q_{8+2L}}|u(n)|²)^{1/2} + a²Fb + aGb)`. -/
theorem value_high [NeZero N] {X : Fin 4 → Site NF → Mat} {α₁ : ℝ} (hX : RegField S X α₁) (hα0 : 0 ≤ α₁)
    (hα : 64 * (S.L : ℝ) ^ 2 * α₁ ≤ 1) (hRM : 8 * (S.L : ℝ) ^ 2 ≤ RMS) {ΩD : Set (Site NF)}
    (hD : ∀ x, S.ef x ∈ S.Ω 1 → x ∈ ΩD) {u f : Fin m → Site NF → Mat} {g : Fin m → Fin 4 → Site NF → Mat}
    {Zu Nu Fu : Fin m → Site NF → Mat} {Zc : Site NF → (Fin 4 → ℤ) → (VS N m →L[ℝ] VS N m)}
    (H : LocalEqn S X ΩD u f g Zu Nu Fu Zc) {x : Site NF} (hj : 2 ≤ jj x) {CN Fb Gb : ℝ} (hCN : 0 ≤ CN)
    (hZs : ∀ z, InQr ((S.L : ℝ) ^ jj x)⁻¹ (xbar x) 8 z →
      ((S.L : ℝ) ^ jj x) ^ 2 * ∑ e ∈ Eoff, ‖Zc (castS z) e‖ ≤ 1 / 4)
    (hN1 : ∀ z, InQr ((S.L : ℝ) ^ jj x)⁻¹ (xbar x) 8 z →
      ‖(sfData S (jj x) u f g Nu Fu Zc).Nu z‖ ≤
        CN * pn ((S.L : ℝ) ^ jj x)⁻¹ (QF ((S.L : ℝ) ^ jj x)⁻¹ (xbar x) (8 + 2 * S.L)) 2 (fun z => ‖SFBox.liftM (N := N) u z‖))
    (hFb : ∀ z, InQr ((S.L : ℝ) ^ jj x)⁻¹ (xbar x) (8 + 2 * S.L) z →
      Real.sqrt (nsq fun k => f k (castS z) + Fu k (castS z)) ≤ Fb)
    (hGb : ∀ μ z, InQr ((S.L : ℝ) ^ jj x)⁻¹ (xbar x) (8 + 2 * S.L) z →
      Real.sqrt (nsq fun k => g k μ (castS z)) ≤ Gb)
    {z : Fin 4 → ℤ} (hz : InQr ((S.L : ℝ) ^ jj x)⁻¹ (xbar x) 4 z) :
    Real.sqrt (nsq fun k => u k (castS z)) ≤ Ksf CN *
      (((S.L : ℝ) ^ jj x)⁻¹ ^ 2 * Real.sqrt (∑ w ∈ QF ((S.L : ℝ) ^ jj x)⁻¹ (xbar x) (8 + 2 * S.L),
        nsq fun k => u k (castS w)) + ((S.L : ℝ) ^ jj x) ^ 2 * Fb + (S.L : ℝ) ^ jj x * Gb) := by
  have Hs := sfHyp_of S hX hα0 hα hRM hD H hj hCN hZs hN1 hFb hGb
  have h := Hs.sf_local_i hz
  simp only [Th, sfData] at h
  rw [norm_liftM, pn_liftM] at h
  have hN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N))
  have e : Ksf CN * (Real.sqrt N * ((S.L : ℝ) ^ jj x)⁻¹ ^ 2 *
      Real.sqrt (∑ w ∈ QF ((S.L : ℝ) ^ jj x)⁻¹ (xbar x) (8 + 2 * S.L), nsq fun k => u k (castS w)) +
      Real.sqrt N * ((S.L : ℝ) ^ jj x) ^ 2 * Fb + Real.sqrt N * (S.L : ℝ) ^ jj x * Gb) =
      Real.sqrt N * (Ksf CN * (((S.L : ℝ) ^ jj x)⁻¹ ^ 2 *
        Real.sqrt (∑ w ∈ QF ((S.L : ℝ) ^ jj x)⁻¹ (xbar x) (8 + 2 * S.L), nsq fun k => u k (castS w)) +
        ((S.L : ℝ) ^ jj x) ^ 2 * Fb + (S.L : ℝ) ^ jj x * Gb)) := by ring
  rw [e] at h
  exact le_of_mul_le_mul_left h hN

end SFBounds
end CoreLean

end
