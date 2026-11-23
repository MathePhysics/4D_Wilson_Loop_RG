/-
`lem:partition-of-unity`(iii) of BALABAN_CORE.tex (`46925ba99aac`): locality and covariance.

* `pu_local`: `h_□` and the membership `□ ∈ 𝒟` are determined by the domains inside the cube with the centre of
  `□` and the side `4Ls_j` (`Cbig`): the cubes of `𝒟` whose functions do not vanish on the support of `φ_□`
  have the scales `j - 1`, `j`, `j + 1` (`scale`), and so lie in that cube, and whether they belong to `𝒟` is
  decided by the domains on their own cubes of the grid.
* `pu_covariant`: for a map `θ` of the torus and a bijection `e` of the cubes with `φ_{e□} ∘ θ = φ_□` and
  `e□ ∈ 𝒟' ⟺ □ ∈ 𝒟`, `h'_{e□} ∘ θ = h_□`; `InD_transfer` gives the second hypothesis when `θ` maps the
  cubes of the grid of `□` onto those of `e□` and the domains `Ω'_i = θΩ_i`.
* `pu_perm`, `pu_refl`, `pu_translate`: the permutations of the coordinates, the reflections `x_μ ↦ -x_μ`, and
  the translations by the points of the grid of side `s_k`, which map every grid to itself.
-/
import CoreLean.PartitionGeometry

open Real Finset
open scoped Classical

noncomputable section

namespace CoreLean
namespace PartitionUnity

local notation "E" => Fin 4 → ℝ

namespace Domains

variable {S : Scales}

/-! ### Locality -/

/-- The cube with the centre of `□` and the side `4Ls_j`. -/
def Cbig (S : Scales) (q : S.Idx) : Set E := {z | dT S.hℓ z (cen (S.s q.1) q.2) ≤ 2 * S.L * S.s q.1}

lemma subset_iff_of_inter {B C Ω Ω' : Set E} (hB : B ⊆ C) (h : Ω ∩ C = Ω' ∩ C) : B ⊆ Ω ↔ B ⊆ Ω' := by
  constructor
  · intro hΩ y hy
    have : y ∈ Ω ∩ C := ⟨hΩ hy, hB hy⟩
    rw [h] at this; exact this.1
  · intro hΩ y hy
    have : y ∈ Ω' ∩ C := ⟨hΩ hy, hB hy⟩
    rw [← h] at this; exact this.1

/-- Membership in `𝒟` is decided by the domains on a set containing the cube of side `2s_i` of the cube. -/
lemma InD_iff_of_local (D D' : Domains S) {C : Set E} (hΩ : ∀ i, D.Ω i ∩ C = D'.Ω i ∩ C)
    (hΩD : D.ΩD ∩ C = D'.ΩD ∩ C) {q' : S.Idx}
    (hC : {y | dT S.hℓ y (cen (S.s q'.1) q'.2) ≤ S.s q'.1} ⊆ C) : D.InD q' ↔ D'.InD q' := by
  have hB : ∀ ε, gcube S q'.1 (gc S q'.1 q'.2 ε) ⊆ C := fun ε y hy => hC (dT_cen_of_mem S hy)
  unfold InD
  refine exists_congr fun ε => ?_
  rw [subset_iff_of_inter (hB ε) (hΩ _), subset_iff_of_inter (hB ε) (hΩ _),
    subset_iff_of_inter (hB ε) hΩD]

/-- **`lem:partition-of-unity`(iii), locality**: two sequences of domains which coincide on the cube with the
centre of `□` and the side `4Ls_j` have the same membership of `□` in `𝒟` and the same function `h_□`. -/
theorem pu_local (D D' : Domains S) (q : S.Idx) (hΩ : ∀ i, D.Ω i ∩ Cbig S q = D'.Ω i ∩ Cbig S q)
    (hΩD : D.ΩD ∩ Cbig S q = D'.ΩD ∩ Cbig S q) : (D.InD q ↔ D'.InD q) ∧ ∀ x, D.hpu q x = D'.hpu q x := by
  have hL := S.L_ge
  have hs := S.s_pos q.1
  set c := cen (S.s q.1) q.2 with hc
  have hq : D.InD q ↔ D'.InD q := InD_iff_of_local D D' hΩ hΩD fun y hy => by
    show dT S.hℓ y c ≤ 2 * S.L * S.s q.1
    have : dT S.hℓ y c ≤ S.s q.1 := hy
    nlinarith
  refine ⟨hq, fun x => ?_⟩
  by_cases hI : D.InD q
  swap
  · simp only [hpu, if_neg hI, if_neg (mt hq.2 hI)]
  have hI' := hq.1 hI
  by_cases hφ : S.φ q x = 0
  · simp only [hpu, if_pos hI, if_pos hI', hφ, zero_div]
  have hxc := S.dT_lt_of_φ_ne hφ
  have hx : dT S.hℓ x c ≤ S.s q.1 := by linarith
  -- a cube of `𝒟` or `𝒟'` whose function does not vanish at `x` lies in the big cube
  have hcube : ∀ (D₀ : Domains S), D₀.InD q → ∀ q', D₀.InD q' → S.φ q' x ≠ 0 →
      {y | dT S.hℓ y (cen (S.s q'.1) q'.2) ≤ S.s q'.1} ⊆ Cbig S q := by
    intro D₀ hI₀ q' hq' hφ' y hy
    have hsc := (D₀.scale hI₀ hq' hx hφ').2
    have hsi : S.s q'.1 ≤ S.L * S.s q.1 := by rw [← S.hsL]; exact S.s_mono hsc
    have hx' := S.dT_lt_of_φ_ne hφ'
    have hy' : dT S.hℓ y (cen (S.s q'.1) q'.2) ≤ S.s q'.1 := hy
    have t1 := dT_triangle S.hℓ y (cen (S.s q'.1) q'.2) x
    have t2 := dT_triangle S.hℓ y x c
    rw [dT_comm S.hℓ (cen (S.s q'.1) q'.2) x] at t1
    show dT S.hℓ y c ≤ 2 * S.L * S.s q.1
    nlinarith
  have hN : D.N2 x = D'.N2 x := by
    unfold N2
    refine Finset.sum_congr rfl fun q' _ => ?_
    by_cases hφ' : S.φ q' x = 0
    · simp [hφ']
    · have h1 : D.InD q' → D'.InD q' := fun h =>
        (InD_iff_of_local D D' hΩ hΩD (hcube D hI q' h hφ')).1 h
      have h2 : D'.InD q' → D.InD q' := fun h =>
        (InD_iff_of_local D D' hΩ hΩD (hcube D' hI' q' h hφ')).2 h
      by_cases h : D.InD q'
      · rw [if_pos h, if_pos (h1 h)]
      · rw [if_neg h, if_neg (mt h2 h)]
  simp only [hpu, if_pos hI, if_pos hI', hN]

/-! ### Covariance -/

/-- **Covariance**, the abstract form: if `φ_{e□} ∘ θ = φ_□` and `e□ ∈ 𝒟' ⟺ □ ∈ 𝒟` for a bijection `e` of the
cubes, then `h'_{e□} ∘ θ = h_□`. -/
theorem pu_covariant (D D' : Domains S) (e : S.Idx ≃ S.Idx) (θ : E → E)
    (hφ : ∀ q x, S.φ (e q) (θ x) = S.φ q x) (hI : ∀ q, D'.InD (e q) ↔ D.InD q) (q : S.Idx) (x : E) :
    D'.hpu (e q) (θ x) = D.hpu q x := by
  have hN : D'.N2 (θ x) = D.N2 x := by
    unfold N2
    rw [← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun q' _ => ?_
    by_cases h : D.InD q'
    · rw [if_pos ((hI q').2 h), if_pos h, hφ]
    · rw [if_neg (mt (hI q').1 h), if_neg h]
  unfold hpu
  by_cases h : D.InD q
  · rw [if_pos ((hI q).2 h), if_pos h, hφ, hN]
  · rw [if_neg (mt (hI q).1 h), if_neg h]

/-- The membership in `𝒟` is transported by a bijection `θ` of the torus which maps the domains of one sequence
onto those of the other and the cubes of the grid of `□` onto those of `□'`. -/
lemma InD_transfer (D D' : Domains S) (θ θi : E → E) (hθi : ∀ x, θi (θ x) = x)
    (hΩ : ∀ i y, y ∈ D'.Ω i ↔ θi y ∈ D.Ω i) (hD : ∀ y, y ∈ D'.ΩD ↔ θi y ∈ D.ΩD) (q q' : S.Idx)
    (hi : (q'.1 : ℕ) = q.1) (f : (Fin 4 → Bool) ≃ (Fin 4 → Bool))
    (hcube : ∀ ε y, y ∈ gcube S q'.1 (gc S q'.1 q'.2 (f ε)) ↔ θi y ∈ gcube S q.1 (gc S q.1 q.2 ε)) :
    D'.InD q' ↔ D.InD q := by
  have key : ∀ ε (Ω Ω' : Set E), (∀ y, y ∈ Ω' ↔ θi y ∈ Ω) →
      (gcube S q'.1 (gc S q'.1 q'.2 (f ε)) ⊆ Ω' ↔ gcube S q.1 (gc S q.1 q.2 ε) ⊆ Ω) := by
    intro ε Ω Ω' hΩΩ
    constructor
    · intro h x hx
      have : θ x ∈ gcube S q'.1 (gc S q'.1 q'.2 (f ε)) := (hcube ε (θ x)).2 (by rwa [hθi])
      have := (hΩΩ _).1 (h this)
      rwa [hθi] at this
    · intro h y hy
      exact (hΩΩ y).2 (h ((hcube ε y).1 hy))
  have hΩ1 : ∀ y, y ∈ D'.Ω q'.1 ↔ θi y ∈ D.Ω q.1 := fun y => by rw [hΩ _ y, hi]
  have hΩ2 : ∀ y, y ∈ D'.Ω ((q'.1 : ℕ) + 1) ↔ θi y ∈ D.Ω ((q.1 : ℕ) + 1) := fun y => by
    rw [hΩ _ y, hi]
  unfold InD
  constructor
  · rintro ⟨ε', h1, h2, h3⟩
    have he : ε' = f (f.symm ε') := (f.apply_symm_apply ε').symm
    rw [he] at h1 h2 h3
    refine ⟨f.symm ε', (key _ _ _ hΩ1).1 h1, fun h => h2 ((key _ _ _ hΩ2).2 h), fun h0 => ?_⟩
    exact (key _ _ _ hD).1 (h3 (by rw [hi]; exact h0))
  · rintro ⟨ε, h1, h2, h3⟩
    refine ⟨f ε, (key _ _ _ hΩ1).2 h1, fun h => h2 ((key _ _ _ hΩ2).1 h), fun h0 => ?_⟩
    exact (key _ _ _ hD).2 (h3 (by rw [← hi]; exact h0))

/-- Two points congruent mod `ℓ` in every coordinate are at the same distance from every point. -/
lemma dT_congr (S : Scales) {a b : E} (h : ∀ μ, ∃ w : ℤ, a μ = b μ + w * S.ℓ) (y : E) :
    dT S.hℓ y a = dT S.hℓ y b := by
  unfold dT
  congr 1
  funext μ
  obtain ⟨w, hw⟩ := h μ
  rw [hw, show y μ - (b μ + w * S.ℓ) = (y μ - b μ) + ((-w : ℤ) : ℝ) * S.ℓ by push_cast; ring, rep_add_int_mul]

/-- An integer representative of a class mod `P`. -/
lemma val_cong {P : ℕ} [NeZero P] (a : ZMod P) (z : ℤ) (h : (z : ZMod P) = a) :
    ∃ w : ℤ, (a.val : ℤ) = z + w * P := by
  have : ((a.val : ℤ) : ZMod P) = (z : ZMod P) := by rw [h]; simp
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at this
  obtain ⟨c, hc⟩ := this
  exact ⟨-c, by linarith⟩

/-! ### The permutations of the coordinates -/

/-- The permutation of the cubes. -/
def ePerm (S : Scales) (σ : Equiv.Perm (Fin 4)) : S.Idx ≃ S.Idx :=
  Equiv.sigmaCongrRight fun i => Equiv.arrowCongr σ (Equiv.refl _)

lemma ePerm_apply (σ : Equiv.Perm (Fin 4)) (q : S.Idx) :
    ePerm S σ q = ⟨q.1, fun ν => q.2 (σ.symm ν)⟩ := rfl

/-- **`lem:partition-of-unity`(iii), the permutations of the coordinates**: for the sequence
`Ω'_i = θΩ_i`, `(θx)_ν = x_{σ⁻¹ν}`, the functions are `h'_{θ□} = h_□ ∘ θ⁻¹`. -/
theorem pu_perm (D D' : Domains S) (σ : Equiv.Perm (Fin 4))
    (hΩ : ∀ i y, y ∈ D'.Ω i ↔ (fun μ => y (σ μ)) ∈ D.Ω i) (hD : ∀ y, y ∈ D'.ΩD ↔ (fun μ => y (σ μ)) ∈ D.ΩD)
    (q : S.Idx) (x : E) : D'.hpu (ePerm S σ q) (fun ν => x (σ.symm ν)) = D.hpu q x := by
  set θ : E → E := fun x ν => x (σ.symm ν) with hθ
  set θi : E → E := fun y μ => y (σ μ) with hθi
  have hθi1 : ∀ x, θi (θ x) = x := fun x => by funext μ; simp [hθ, hθi]
  have hθi2 : ∀ y, θ (θi y) = y := fun y => by funext ν; simp [hθ, hθi]
  have hφ : ∀ q x, S.φ (ePerm S σ q) (θ x) = S.φ q x := fun q x => by
    unfold Scales.φ phiT
    rw [ePerm_apply]
    exact Equiv.prod_comp σ.symm (fun μ => gT S.hℓ (S.s q.1) (cen (S.s q.1) q.2 μ) (x μ))
  have hdT : ∀ a b : E, dT S.hℓ (θi a) (θi b) = dT S.hℓ a b := fun a b => by
    refine le_antisymm ((dT_le_iff S.hℓ).2 fun μ => le_dT S.hℓ a b (σ μ)) ((dT_le_iff S.hℓ).2 fun ν => ?_)
    have := le_dT S.hℓ (θi a) (θi b) (σ.symm ν)
    simpa [hθi] using this
  refine pu_covariant D D' (ePerm S σ) θ hφ (fun q => ?_) q x
  refine InD_transfer D D' θ θi hθi1 hΩ hD q (ePerm S σ q) rfl (Equiv.arrowCongr σ (Equiv.refl _))
    fun ε y => ?_
  -- the cube of the grid of `θ□` is the image of that of `□`
  have hgc : gc S (ePerm S σ q).1 (ePerm S σ q).2 (Equiv.arrowCongr σ (Equiv.refl _) ε) =
      θ (gc S q.1 q.2 ε) := by
    funext ν; simp [gc, ePerm_apply, hθ, cen, Equiv.arrowCongr_apply]
  simp only [gcube, Set.mem_setOf_eq, hgc]
  rw [← hdT, hθi1]
  rfl

/-! ### The reflections -/

/-- The reflection `x_μ ↦ -x_μ`. -/
def reflE (μ : Fin 4) (x : E) : E := fun ν => if ν = μ then -x ν else x ν

lemma reflE_invol (μ : Fin 4) (x : E) : reflE μ (reflE μ x) = x := by
  funext ν; by_cases h : ν = μ <;> simp [reflE, h]

/-- The reflection of the corners: `n_μ ↦ -n_μ - 1`, so that `s(n + ½) ↦ -s(n + ½)`. -/
def reflN {P : ℕ} (μ : Fin 4) (n : Fin 4 → ZMod P) : Fin 4 → ZMod P :=
  fun ν => if ν = μ then -n ν - 1 else n ν

lemma reflN_invol {P : ℕ} (μ : Fin 4) (n : Fin 4 → ZMod P) : reflN μ (reflN μ n) = n := by
  funext ν; by_cases h : ν = μ <;> simp [reflN, h]

def reflB (μ : Fin 4) (ε : Fin 4 → Bool) : Fin 4 → Bool := fun ν => if ν = μ then !ε ν else ε ν

lemma reflB_invol (μ : Fin 4) (ε : Fin 4 → Bool) : reflB μ (reflB μ ε) = ε := by
  funext ν; by_cases h : ν = μ <;> simp [reflB, h]

/-- The reflection of the cubes of the grid at a corner. -/
def reflBe (μ : Fin 4) : (Fin 4 → Bool) ≃ (Fin 4 → Bool) := ⟨reflB μ, reflB μ, reflB_invol μ, reflB_invol μ⟩

lemma reflBe_apply (μ : Fin 4) (ε : Fin 4 → Bool) : reflBe μ ε = reflB μ ε := rfl

/-- The reflection of the cubes. -/
def eRefl (S : Scales) (μ : Fin 4) : S.Idx ≃ S.Idx :=
  Equiv.sigmaCongrRight fun i => (Function.Involutive.toPerm (reflN μ) (reflN_invol μ))

lemma eRefl_apply (μ : Fin 4) (q : S.Idx) : eRefl S μ q = ⟨q.1, reflN μ q.2⟩ := rfl

/-- The reflected corner is congruent to minus the corner. -/
lemma corner_reflN (i : Fin (S.k + 1)) (n : ZMod (S.P i)) :
    ∃ w : ℤ, corner (S.s i) (-n - 1) = -corner (S.s i) n + w * S.ℓ := by
  obtain ⟨w, hw⟩ := val_cong (-n - 1) (-(n.val : ℤ) - 1) (by push_cast; simp)
  refine ⟨w, ?_⟩
  have hw' : (((-n - 1 : ZMod (S.P i)).val : ℕ) : ℝ) = -(n.val : ℝ) - 1 + w * S.P i := by exact_mod_cast hw
  rw [corner, corner, hw', S.hP' i]; ring

/-- **`lem:partition-of-unity`(iii), the reflections**: for the sequence `Ω'_i = RΩ_i`, `R` the reflection
`x_μ ↦ -x_μ`, the functions are `h'_{R□} = h_□ ∘ R`. -/
theorem pu_refl (D D' : Domains S) (μ : Fin 4) (hΩ : ∀ i y, y ∈ D'.Ω i ↔ reflE μ y ∈ D.Ω i)
    (hD : ∀ y, y ∈ D'.ΩD ↔ reflE μ y ∈ D.ΩD) (q : S.Idx) (x : E) :
    D'.hpu (eRefl S μ q) (reflE μ x) = D.hpu q x := by
  have hφ : ∀ q x, S.φ (eRefl S μ q) (reflE μ x) = S.φ q x := fun q x => by
    unfold Scales.φ phiT
    rw [eRefl_apply]
    refine Finset.prod_congr rfl fun ν _ => ?_
    simp only [cen, reflN, reflE]
    by_cases h : ν = μ
    · simp only [if_pos h]
      obtain ⟨w, hw⟩ := corner_reflN q.1 (q.2 ν)
      unfold gT
      apply prof_congr_abs (S.s_pos _)
      rw [hw, show -x ν - (-corner (S.s q.1) (q.2 ν) + w * S.ℓ) =
        -(x ν - corner (S.s q.1) (q.2 ν)) + ((-w : ℤ) : ℝ) * S.ℓ by push_cast; ring, rep_add_int_mul,
        abs_rep_neg]
    · simp only [if_neg h]
  have hdT : ∀ a b : E, dT S.hℓ (reflE μ a) (reflE μ b) = dT S.hℓ a b := fun a b => by
    unfold dT
    congr 1
    funext ν
    by_cases h : ν = μ
    · simp only [reflE, if_pos h]
      rw [show -a ν - -b ν = -(a ν - b ν) by ring, abs_rep_neg]
    · simp only [reflE, if_neg h]
  refine pu_covariant D D' (eRefl S μ) (reflE μ) hφ (fun q => ?_) q x
  refine InD_transfer D D' (reflE μ) (reflE μ) (reflE_invol μ) hΩ hD q (eRefl S μ q) rfl
    (reflBe μ) fun ε y => ?_
  -- the cube of the grid of `R□` is congruent to the image of that of `□`
  have hcong : ∀ ν, ∃ w : ℤ, gc S (eRefl S μ q).1 (eRefl S μ q).2 (reflB μ ε) ν =
      reflE μ (gc S q.1 q.2 ε) ν + w * S.ℓ := by
    intro ν
    simp only [gc, eRefl_apply, cen, reflN, reflB, reflE]
    by_cases h : ν = μ
    · simp only [if_pos h]
      obtain ⟨w, hw⟩ := corner_reflN q.1 (q.2 ν)
      refine ⟨w, ?_⟩
      rw [hw]
      cases hε : ε ν <;> simp <;> ring
    · exact ⟨0, by simp [if_neg h]⟩
  simp only [gcube, Set.mem_setOf_eq, reflBe_apply]
  rw [dT_congr S hcong, ← hdT, reflE_invol]
  exact Iff.rfl

/-! ### The translations -/

lemma s_add_pow (S : Scales) (i d : ℕ) : S.s (i + d) = (S.L : ℝ) ^ d * S.s i := by
  induction d with
  | zero => simp
  | succ d ih => rw [← add_assoc, S.hsL, ih]; ring

/-- The translation of the cubes by `t = s_k m`. -/
def eTrans (S : Scales) (m : Fin 4 → ℤ) : S.Idx ≃ S.Idx :=
  Equiv.sigmaCongrRight fun i =>
    Equiv.addRight (fun μ => (((S.L : ℤ) ^ (S.k - i) * m μ : ℤ) : ZMod (S.P i)))

lemma eTrans_apply (m : Fin 4 → ℤ) (q : S.Idx) :
    eTrans S m q = ⟨q.1, q.2 + fun μ => (((S.L : ℤ) ^ (S.k - q.1) * m μ : ℤ) : ZMod (S.P q.1))⟩ := rfl

/-- The translated corner is congruent to the corner plus `t_μ = s_k m_μ`. -/
lemma corner_trans (m : Fin 4 → ℤ) (i : Fin (S.k + 1)) (n : ZMod (S.P i)) (μ : Fin 4) :
    ∃ w : ℤ, corner (S.s i) (n + (((S.L : ℤ) ^ (S.k - i) * m μ : ℤ) : ZMod (S.P i))) =
      corner (S.s i) n + S.s S.k * m μ + w * S.ℓ := by
  obtain ⟨w, hw⟩ := val_cong (n + (((S.L : ℤ) ^ (S.k - i) * m μ : ℤ) : ZMod (S.P i)))
    ((n.val : ℤ) + (S.L : ℤ) ^ (S.k - i) * m μ) (by push_cast; simp)
  refine ⟨w, ?_⟩
  have hw' : ((n + (((S.L : ℤ) ^ (S.k - i) * m μ : ℤ) : ZMod (S.P i))).val : ℝ) =
      (n.val : ℝ) + (S.L : ℝ) ^ (S.k - i) * m μ + w * S.P i := by exact_mod_cast hw
  have hk : S.s S.k = (S.L : ℝ) ^ (S.k - i) * S.s i := by
    rw [← s_add_pow, Nat.add_sub_cancel' (Nat.lt_succ_iff.1 i.2)]
  rw [corner, corner, hw', hk, S.hP' i]; ring

/-- **`lem:partition-of-unity`(iii), the translations**: for the translation `θx = x + t` by a point
`t = s_k m` of the grid of the largest side, which maps every grid to itself, and the sequence
`Ω'_i = Ω_i + t`, the functions are `h'_{θ□} = h_□ ∘ θ⁻¹`. -/
theorem pu_translate (D D' : Domains S) (m : Fin 4 → ℤ)
    (hΩ : ∀ i y, y ∈ D'.Ω i ↔ (y - fun μ => S.s S.k * m μ) ∈ D.Ω i)
    (hD : ∀ y, y ∈ D'.ΩD ↔ (y - fun μ => S.s S.k * m μ) ∈ D.ΩD) (q : S.Idx) (x : E) :
    D'.hpu (eTrans S m q) (x + fun μ => S.s S.k * m μ) = D.hpu q x := by
  set t : E := fun μ => S.s S.k * m μ with ht
  have hφ : ∀ q x, S.φ (eTrans S m q) (x + t) = S.φ q x := fun q x => by
    unfold Scales.φ phiT
    rw [eTrans_apply]
    refine Finset.prod_congr rfl fun ν _ => ?_
    obtain ⟨w, hw⟩ := corner_trans m q.1 (q.2 ν) ν
    simp only [cen, Pi.add_apply]
    unfold gT
    rw [hw, show x ν + t ν - (corner (S.s q.1) (q.2 ν) + S.s S.k * m ν + w * S.ℓ) =
      (x ν - corner (S.s q.1) (q.2 ν)) + ((-w : ℤ) : ℝ) * S.ℓ by rw [ht]; push_cast; ring, rep_add_int_mul]
  have hdT : ∀ a b : E, dT S.hℓ (a - t) (b - t) = dT S.hℓ a b := fun a b => by
    unfold dT; congr 1; funext ν; simp only [Pi.sub_apply]; ring_nf
  refine pu_covariant D D' (eTrans S m) (fun x => x + t) hφ (fun q => ?_) q x
  refine InD_transfer D D' (fun x => x + t) (fun y => y - t) (fun x => by simp) hΩ hD q (eTrans S m q) rfl
    (Equiv.refl _) fun ε y => ?_
  have hcong : ∀ ν, ∃ w : ℤ, gc S (eTrans S m q).1 (eTrans S m q).2 ε ν =
      (gc S q.1 q.2 ε + t) ν + w * S.ℓ := by
    intro ν
    obtain ⟨w, hw⟩ := corner_trans m q.1 (q.2 ν) ν
    refine ⟨w, ?_⟩
    simp only [gc, eTrans_apply, cen, Pi.add_apply, hw, ht]
    ring
  simp only [gcube, Set.mem_setOf_eq, Equiv.refl_apply]
  rw [dT_congr S hcong, ← hdT, add_sub_cancel_right]
  exact Iff.rfl

end Domains

end PartitionUnity
end CoreLean

end
