/-
`prop:sf-vector-lower` of BALABAN_CORE.tex (`95f07f48317e`), the step "The double commutators": the partition of unity
of `lem:partition-of-unity` (`PartitionGeometry.lean`, on `ℝ⁴` with the torus distance `dT`) for a sequence of domains
and on its fine lattice.

* `abs_rep_eq_norm`, `dT_eq_norm`: `dT(x, y) = ‖π(x) - π(y)‖` on the torus `(ℝ/ℓℤ)⁴`.
-/
import CoreLean.SFIMS
import CoreLean.PartitionLocality

open Finset

noncomputable section

namespace CoreLean
namespace PartitionUnity

variable {ℓ : ℝ} (hℓ : 0 < ℓ)

/-- **`|rep t| = ‖t‖` on the circle `ℝ/ℓℤ`.** -/
lemma abs_rep_eq_norm (t : ℝ) : |rep hℓ t| = ‖((t : ℝ) : AddCircle ℓ)‖ := by
  obtain ⟨n, hn⟩ := rep_eq_sub hℓ t
  have e : ((t : ℝ) : AddCircle ℓ) = ((rep hℓ t : ℝ) : AddCircle ℓ) := by
    rw [hn, AddCircle.coe_sub]
    have h0 : (((n : ℝ) * ℓ : ℝ) : AddCircle ℓ) = 0 :=
      (AddCircle.coe_eq_zero_iff ℓ).2 ⟨n, by simp [zsmul_eq_mul]⟩
    rw [h0, sub_zero]
  rw [e]
  have hm := rep_mem hℓ t
  refine ((AddCircle.norm_coe_eq_abs_iff (p := ℓ) hℓ.ne').2 ?_).symm
  rw [abs_of_pos hℓ, abs_le]; constructor <;> linarith [hm.1, hm.2]

/-- **The torus distance**: `dT(x, y) = ‖π(x) - π(y)‖`. -/
theorem dT_eq_norm (x y : Fin 4 → ℝ) : dT hℓ x y = ‖projT ℓ x - projT ℓ y‖ := by
  unfold dT
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun μ _ => ?_
    rw [abs_rep_eq_norm hℓ, AddCircle.coe_sub]
    exact norm_le_pi_norm (projT ℓ x - projT ℓ y) μ
  · refine (pi_norm_le_iff_of_nonneg (by
      exact (abs_nonneg _).trans (Finset.le_sup' (fun μ => |rep hℓ (x μ - y μ)|) (mem_univ 0)))).2 fun μ => ?_
    show ‖((x μ : ℝ) : AddCircle ℓ) - ((y μ : ℝ) : AddCircle ℓ)‖ ≤ _
    rw [← AddCircle.coe_sub, ← abs_rep_eq_norm hℓ]
    exact Finset.le_sup' (fun μ => |rep hℓ (x μ - y μ)|) (mem_univ μ)

end PartitionUnity
namespace PartitionUnity

open Lattices

variable (S : Lattices.SeqDom)

lemma P_eq {i : ℕ} (hi : i ≤ S.k) :
    ellT S.L S.mT = ((2 * S.L ^ (S.mT - S.mM + S.k - i) : ℕ) : ℝ) * (((S.L ^ S.mM : ℕ) : ℝ) * sp S.L S.k i) := by
  have hL : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  have hmM := S.mM_le
  unfold ellT sp eta
  push_cast
  have e : S.mT = (S.mT - S.mM + S.k - i) + S.mM + i - S.k := by omega
  have e2 : (S.mT - S.mM + S.k - i) + S.mM + i = S.mT + S.k := by omega
  have h1 : (S.L : ℝ) ^ (S.mT - S.mM + S.k - i) * (S.L : ℝ) ^ S.mM * (S.L : ℝ) ^ i = (S.L : ℝ) ^ S.mT * (S.L : ℝ) ^ S.k := by
    rw [← pow_add, ← pow_add, e2, pow_add]
  field_simp
  linear_combination (-1 : ℝ) * h1

/-- **The scales of a sequence of domains** for `lem:partition-of-unity`: `s_i = Ma_i`, `ℓ = 2L^{m_𝕋}`, `η = a₀`. -/
def toScales (hM : 12 ≤ S.L ^ S.mM) (hR : 12 * S.L ≤ S.R) : Scales where
  L := S.L
  k := S.k
  ℓ := ellT S.L S.mT
  s := fun i => ((S.L ^ S.mM : ℕ) : ℝ) * sp S.L S.k i
  P := fun i => 2 * S.L ^ (S.mT - S.mM + S.k - i)
  η := eta S.L S.k
  R := S.R
  hL := by have := S.three_le_L; omega
  hℓ := by unfold ellT; have := S.Lpos; positivity
  hs0 := by have := S.Lpos; unfold sp eta; positivity
  hsL := fun i => by simp only [sp, pow_succ]; push_cast; ring
  hP := fun i hi => ⟨by have := S.Lpos; have : 1 ≤ S.L ^ (S.mT - S.mM + S.k - i) := Nat.one_le_pow _ _ S.Lpos; omega,
    P_eq S hi⟩
  hη := eta_pos S.Lpos
  hηs := by
    have he := eta_pos (k := S.k) S.Lpos
    simp only [sp, pow_zero, one_mul]
    have : (12 : ℝ) ≤ ((S.L ^ S.mM : ℕ) : ℝ) := by exact_mod_cast hM
    nlinarith
  hR := by exact_mod_cast hR

end PartitionUnity

namespace PartitionUnity

open Lattices

variable (S : Lattices.SeqDom) (hM : 12 ≤ S.L ^ S.mM) (hR : 12 * S.L ≤ S.R)

/-- **The domains of a sequence** for `lem:partition-of-unity`, with the torus as the Dirichlet domain. -/
def toDomains : Domains (toScales S hM hR) where
  Ω := fun i => {x | projT (ellT S.L S.mT) x ∈ S.Ω i}
  ΩD := Set.univ
  hΩ0 := by ext x; simp [S.Ω_zero]
  hanti := fun i x hx => S.Ω_succ i hx
  hΩk := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    show projT (ellT S.L S.mT) x ∉ S.Ω (S.k + 1)
    rw [S.Ω_top (S.k + 1) (Nat.lt_succ_self _)]; exact Set.notMem_empty _
  hgrid := fun i hi1 hik x hx => by
    obtain ⟨C, hC, hΩ⟩ := S.cubes i hi1 hik
    have hx' : projT (ellT S.L S.mT) x ∈ S.Ω i := hx
    rw [hΩ] at hx'
    obtain ⟨c, hcC, hxc⟩ := Set.mem_iUnion₂.1 hx'
    have hc := hC hcC
    choose m hm using hc
    refine ⟨fun μ => (m μ : ℝ) * (((S.L ^ S.mM : ℕ) : ℝ) * sp S.L S.k i), fun μ => ⟨m μ, by
      show (m μ : ℝ) * (((S.L ^ S.mM : ℕ) : ℝ) * sp S.L S.k i) = (((S.L ^ S.mM : ℕ) : ℝ) * sp S.L S.k i) * m μ
      ring⟩, ?_, ?_⟩
    · have hproj : projT (ellT S.L S.mT) (fun μ => (m μ : ℝ) * (((S.L ^ S.mM : ℕ) : ℝ) * sp S.L S.k i)) = c := by
        funext μ; rw [hm μ]; rfl
      show dT _ x _ ≤ _
      rw [dT_eq_norm]
      change ‖projT (ellT S.L S.mT) x - projT (ellT S.L S.mT) _‖ ≤ ((S.L ^ S.mM : ℕ) : ℝ) * sp S.L S.k i / 2
      rw [hproj, ← dist_eq_norm]
      exact Metric.mem_closedBall.1 hxc
    · intro y hy
      have hproj : projT (ellT S.L S.mT) (fun μ => (m μ : ℝ) * (((S.L ^ S.mM : ℕ) : ℝ) * sp S.L S.k i)) = c := by
        funext μ; rw [hm μ]; rfl
      have hy' : dT (toScales S hM hR).hℓ y _ ≤ _ := hy
      rw [dT_eq_norm] at hy'
      change ‖projT (ellT S.L S.mT) y - projT (ellT S.L S.mT) _‖ ≤ ((S.L ^ S.mM : ℕ) : ℝ) * sp S.L S.k i / 2 at hy'
      rw [hproj, ← dist_eq_norm] at hy'
      show projT (ellT S.L S.mT) y ∈ S.Ω i
      rw [hΩ]
      exact Set.mem_iUnion₂.2 ⟨c, hcC, Metric.mem_closedBall.2 hy'⟩
  hsep := fun i hi1 hik y hy y' hy' => by
    have h := S.sep i hi1 hik ⟨_, hy⟩ ⟨_, hy'⟩
    have h2 := setDist_le (A := (S.Ω i)ᶜ) (B := S.Ω (i + 1)) hy hy'
    show (S.R : ℝ) * (((S.L ^ S.mM : ℕ) : ℝ) * sp S.L S.k i) < dT _ y y'
    rw [dT_eq_norm, ← dist_eq_norm]
    have e : ((S.R * S.L ^ S.mM : ℕ) : ℝ) * sp S.L S.k i = (S.R : ℝ) * (((S.L ^ S.mM : ℕ) : ℝ) * sp S.L S.k i) := by
      push_cast; ring
    rw [← e]
    exact h.trans_le h2
  hD := Or.inl rfl

end PartitionUnity

namespace PartitionUnity

open Lattices

variable (S : Lattices.SeqDom) (hM : 12 ≤ S.L ^ S.mM) (hR : 12 * S.L ≤ S.R)

local notation "NF" => SequenceAverages.N0 S

/-- The point `xη` of `ℝ⁴` of a fine site. -/
def liftE (x : Site NF) : Fin 4 → ℝ := fun μ => ((x μ).val : ℝ) * eta S.L S.k

lemma projT_liftE (x : Site NF) : projT (ellT S.L S.mT) (liftE S x) = S.ef x := rfl

lemma dT_liftE (x x' : Site NF) :
    dT (toScales S hM hR).hℓ (liftE S x) (liftE S x') = (Blocks.dinf x x' : ℝ) * eta S.L S.k := by
  rw [dT_eq_norm]
  change ‖projT (ellT S.L S.mT) (liftE S x) - projT (ellT S.L S.mT) (liftE S x')‖ = _
  rw [projT_liftE, projT_liftE]
  exact norm_emb_sub S.Lpos (SequenceAverages.N0_eq S) x x'

/-- **The partition of unity on the fine lattice**: `h_□(x) = h_□(xη)`. -/
def hL (q : (toScales S hM hR).Idx) (x : Site NF) : ℝ := (toDomains S hM hR).hpu q (liftE S x)

lemma hL_sum (x : Site NF) : ∑ q, hL S hM hR q x ^ 2 = 1 := (toDomains S hM hR).pu_sum (Set.mem_univ _)

lemma hL_mem (q : (toScales S hM hR).Idx) (x : Site NF) : 0 ≤ hL S hM hR q x ∧ hL S hM hR q x ≤ 1 :=
  (toDomains S hM hR).pu_mem q _

/-- The constant of the Lipschitz bound of the partition of unity. -/
def Cpu (L : ℕ) : ℝ := 776 * max prof_lip.choose 3 * L + 3

lemma Cpu_nonneg (L : ℕ) : 0 ≤ Cpu L := by
  unfold Cpu
  have : 0 ≤ max prof_lip.choose 3 := le_max_of_le_right (by norm_num)
  positivity

/-- **The Lipschitz bound on the fine lattice**: `|h_□(x) - h_□(x')| ≤ C_pu dinf(x, x')/(ML^i)`, `i` the scale of
`□`. -/
theorem hL_lip (q : (toScales S hM hR).Idx) (x x' : Site NF) :
    |hL S hM hR q x - hL S hM hR q x'| ≤ Cpu S.L / ((S.L : ℝ) ^ S.mM * (S.L : ℝ) ^ (q.1 : ℕ)) * Blocks.dinf x x' := by
  have hC := prof_lip.choose_spec
  have h := (toDomains S hM hR).pu_lip hC.1 hC.2 q (liftE S x) (liftE S x')
  rw [dT_liftE] at h
  have he : 0 < eta S.L S.k := eta_pos S.Lpos
  have hs : (toScales S hM hR).s q.1 = ((S.L ^ S.mM : ℕ) : ℝ) * ((S.L : ℝ) ^ (q.1 : ℕ) * eta S.L S.k) := rfl
  unfold hL
  refine h.trans (le_of_eq ?_)
  rw [hs]
  unfold Cpu
  show (776 * max prof_lip.choose 3 * (S.L : ℝ) + 3) / _ * _ = _
  have hL0 : (0 : ℝ) < S.L := by exact_mod_cast S.Lpos
  push_cast
  field_simp

end PartitionUnity

namespace PartitionUnity

/-- **The scales at a site of the support of `h_□`**: for a cube of the index `i`, the site lies in `Ω_{i-1}` and not
in `Ω_{i+2}` (by the separation, `R ≥ 12L`). -/
theorem hpu_scale {S : Scales} (D : Domains S) {q : S.Idx} {z : Fin 4 → ℝ} (h : D.hpu q z ≠ 0) :
    ((1 : ℕ) ≤ (q.1 : ℕ) → z ∈ D.Ω ((q.1 : ℕ) - 1)) ∧ z ∉ D.Ω ((q.1 : ℕ) + 2) := by
  have hI : D.InD q := by by_contra hI; exact h (by unfold Domains.hpu; rw [if_neg hI])
  have hφ : S.φ q z ≠ 0 := by
    intro h0; exact h (by unfold Domains.hpu; rw [if_pos hI, h0, zero_div])
  have hz := S.dT_lt_of_φ_ne hφ
  obtain ⟨ε, hsub, hnot, -⟩ := hI
  obtain ⟨p, hp, hpn⟩ := Set.not_subset.1 hnot
  have hpi : p ∈ D.Ω q.1 := hsub hp
  have hpc := dT_cen_of_mem S hp
  have hs := S.s_pos q.1
  have hd : dT S.hℓ z p < 2 * S.s q.1 := by
    have := dT_triangle S.hℓ z (cen (S.s q.1) q.2) p
    rw [dT_comm S.hℓ (cen (S.s q.1) q.2) p] at this
    linarith
  have hR := S.hR
  have hL := S.L_ge
  have hq := Nat.lt_succ_iff.1 q.1.2
  constructor
  · intro hq1
    by_contra hzn
    rcases Nat.lt_or_ge ((q.1 : ℕ) - 1) 1 with h0 | h0
    · apply hzn; rw [show (q.1 : ℕ) - 1 = 0 by omega, D.hΩ0]; trivial
    · have hsep := D.hsep ((q.1 : ℕ) - 1) h0 (by omega) z hzn p (by rw [show (q.1 : ℕ) - 1 + 1 = q.1 by omega]; exact hpi)
      have hsL : S.s q.1 = S.L * S.s ((q.1 : ℕ) - 1) := by
        rw [← S.hsL]; congr 1; omega
      have hs1 := S.s_pos ((q.1 : ℕ) - 1)
      rw [hsL] at hd
      nlinarith
  · intro hz2
    rcases Nat.lt_or_ge ((q.1 : ℕ) + 1) S.k with h0 | h0
    · have hsep := D.hsep ((q.1 : ℕ) + 1) (by omega) h0 p hpn z hz2
      rw [dT_comm] at hsep
      have h3 : S.s q.1 ≤ S.s ((q.1 : ℕ) + 1) := S.s_mono (by omega)
      have : (2 : ℝ) ≤ S.R := by nlinarith
      nlinarith
    · have : D.Ω ((q.1 : ℕ) + 2) ⊆ D.Ω (S.k + 1) := D.anti_le (by omega)
      rw [D.hΩk] at this
      exact this hz2

end PartitionUnity

namespace PartitionUnity

open Lattices

variable (S : Lattices.SeqDom) (hM : 12 ≤ S.L ^ S.mM) (hR : 12 * S.L ≤ S.R)

local notation "NF" => SequenceAverages.N0 S

/-- **The scale of a site of the support of `h_□`**: `i - 1 ≤ j(x) ≤ i + 1` for a cube of the index `i`. -/
theorem hL_scale {q : (toScales S hM hR).Idx} {x : Site NF} (h : hL S hM hR q x ≠ 0) :
    (q.1 : ℕ) ≤ (S.toDomSeq).sc x + 1 ∧ (S.toDomSeq).sc x ≤ (q.1 : ℕ) + 1 := by
  obtain ⟨h1, h2⟩ := hpu_scale (toDomains S hM hR) h
  constructor
  · rcases Nat.eq_zero_or_pos (q.1 : ℕ) with h0 | h0
    · omega
    · have hx : x ∈ (S.toDomSeq).Ω ((q.1 : ℕ) - 1) := h1 h0
      have := ((S.toDomSeq).mem_iff x _).1 hx
      omega
  · by_contra hc
    have hx : x ∈ (S.toDomSeq).Ω ((q.1 : ℕ) + 2) := ((S.toDomSeq).mem_iff x _).2 (by omega)
    exact h2 hx

end PartitionUnity

namespace PartitionUnity

open Lattices

variable (S : Lattices.SeqDom) (hM : 12 ≤ S.L ^ S.mM) (hR : 12 * S.L ≤ S.R)

local notation "NF" => SequenceAverages.N0 S

open Classical in
/-- **At most `48` of the `h_□` do not vanish at a site.** -/
theorem card_hL (x : Site NF) : ((Finset.univ : Finset (toScales S hM hR).Idx).filter fun q => hL S hM hR q x ≠ 0).card ≤ 48 := by
  set D := toDomains S hM hR
  have hsum := hL_sum S hM hR x
  obtain ⟨q0, -, hq0⟩ : ∃ q0 ∈ (Finset.univ : Finset (toScales S hM hR).Idx), hL S hM hR q0 x ^ 2 ≠ 0 := by
    by_contra hc; push_neg at hc
    rw [Finset.sum_eq_zero hc] at hsum; norm_num at hsum
  have hq0' : D.hpu q0 (liftE S x) ≠ 0 := fun h => hq0 (by unfold hL; rw [h]; ring)
  have hI : D.InD q0 := by by_contra hI; exact hq0' (by unfold Domains.hpu; rw [if_neg hI])
  have hφ : (toScales S hM hR).φ q0 (liftE S x) ≠ 0 := by
    intro h0; exact hq0' (by unfold Domains.hpu; rw [if_pos hI, h0, zero_div])
  have hd := (toScales S hM hR).dT_lt_of_φ_ne hφ
  have hc := D.card_T_le hI (x := liftE S x) (by linarith [(toScales S hM hR).s_pos q0.1])
  refine (Finset.card_le_card fun q hq => ?_).trans hc
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
  simp only [Domains.T, Finset.mem_filter, Finset.mem_univ, true_and]
  have hq' : D.hpu q (liftE S x) ≠ 0 := hq
  have hIq : D.InD q := by by_contra hI; exact hq' (by unfold Domains.hpu; rw [if_neg hI])
  refine ⟨hIq, fun h0 => hq' (by unfold Domains.hpu; rw [if_pos hIq, h0, zero_div])⟩

/-- **Neighbouring sites have scales which differ by at most one** (for `L < RM`). -/
lemma sc_unit (hRM : (S.L : ℝ) < ((S.R * S.L ^ S.mM : ℕ) : ℝ)) (x : Site NF) (μ : Fin 4) :
    (S.toDomSeq).sc (x + CoreLean.unit NF μ) ≤ (S.toDomSeq).sc x + 1 ∧
      (S.toDomSeq).sc x ≤ (S.toDomSeq).sc (x + CoreLean.unit NF μ) + 1 := by
  have hRM1 : 1 ≤ S.R * S.L ^ S.mM := by
    have h : (1 : ℝ) ≤ S.L := by exact_mod_cast S.Lpos
    have : (1 : ℝ) < ((S.R * S.L ^ S.mM : ℕ) : ℝ) := lt_of_le_of_lt h hRM
    exact_mod_cast this.le
  have h1 := S.sc_sub_le_dF x (x + CoreLean.unit NF μ)
  have h2 := (SFBounds.dF_unit_le S hRM1 x μ).1
  have hpos : (0 : ℝ) < ((S.R * S.L ^ S.mM : ℕ) : ℝ) := lt_of_le_of_lt (Nat.cast_nonneg _) hRM
  have h3 : S.dF x (x + CoreLean.unit NF μ) / ((S.R * S.L ^ S.mM : ℕ) : ℝ) < 1 := by
    rw [div_lt_one hpos]; linarith
  have h4 : |((S.toDomSeq).sc x : ℝ) - (S.toDomSeq).sc (x + CoreLean.unit NF μ)| < 2 := by linarith
  rw [abs_lt] at h4
  constructor
  · have : ((S.toDomSeq).sc (x + CoreLean.unit NF μ) : ℝ) < (S.toDomSeq).sc x + 2 := by linarith
    have : (S.toDomSeq).sc (x + CoreLean.unit NF μ) < (S.toDomSeq).sc x + 2 := by exact_mod_cast this
    omega
  · have : ((S.toDomSeq).sc x : ℝ) < (S.toDomSeq).sc (x + CoreLean.unit NF μ) + 2 := by linarith
    have : (S.toDomSeq).sc x < (S.toDomSeq).sc (x + CoreLean.unit NF μ) + 2 := by exact_mod_cast this
    omega

open Classical in
/-- **The sum of the squared differences at a bond**:
`Σ_□(h_□(x + e_μ) - h_□(x))² ≤ 96C_pu²L⁴M^{-2}L^{-2j(x)}`. -/
theorem sum_hL_diff_sq (hRM : (S.L : ℝ) < ((S.R * S.L ^ S.mM : ℕ) : ℝ)) (x : Site NF) (μ : Fin 4) :
    ∑ q, (hL S hM hR q (x + CoreLean.unit NF μ) - hL S hM hR q x) ^ 2 ≤
      96 * Cpu S.L ^ 2 * (S.L : ℝ) ^ 4 / ((S.L : ℝ) ^ S.mM) ^ 2 * ((S.L : ℝ) ^ (2 * (S.toDomSeq).sc x))⁻¹ := by
  set x' := x + CoreLean.unit NF μ
  set T1 := (Finset.univ : Finset (toScales S hM hR).Idx).filter fun q => hL S hM hR q x ≠ 0
  set T2 := (Finset.univ : Finset (toScales S hM hR).Idx).filter fun q => hL S hM hR q x' ≠ 0
  have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast S.Lpos
  have hL0 : (0 : ℝ) < S.L := by linarith
  have hsc := sc_unit S hRM x μ
  -- each term
  have hd1 : (Blocks.dinf x' x : ℝ) ≤ 1 := by
    have : Blocks.dinf x' x ≤ 1 := by
      unfold Blocks.dinf
      refine Finset.sup_le fun ν _ => ?_
      simp only [x', Pi.add_apply, add_sub_cancel_left, CoreLean.unit]
      by_cases h : ν = μ
      · subst h; simp only [Pi.single_eq_same]
        have := Blocks.cd_intCast_le (N := NF) (1 : ℤ)
        simpa using this
      · simp [Pi.single_eq_of_ne h, Blocks.cd_zero]
    exact_mod_cast this
  have hterm : ∀ q ∈ T1 ∪ T2, (hL S hM hR q x' - hL S hM hR q x) ^ 2 ≤
      Cpu S.L ^ 2 * (S.L : ℝ) ^ 4 / ((S.L : ℝ) ^ S.mM) ^ 2 * ((S.L : ℝ) ^ (2 * (S.toDomSeq).sc x))⁻¹ := by
    intro q hq
    have hlip := hL_lip S hM hR q x' x
    have hsc2 : (S.toDomSeq).sc x ≤ (S.toDomSeq).sc x' + 1 := hsc.2
    have hscq : (S.toDomSeq).sc x ≤ (q.1 : ℕ) + 2 := by
      rcases Finset.mem_union.1 hq with hq | hq
      · have := hL_scale S hM hR (Finset.mem_filter.1 hq).2; omega
      · have := hL_scale S hM hR (Finset.mem_filter.1 hq).2; omega
    have hpow : ((S.L : ℝ) ^ (q.1 : ℕ))⁻¹ ^ 2 ≤ (S.L : ℝ) ^ 4 * ((S.L : ℝ) ^ (2 * (S.toDomSeq).sc x))⁻¹ := by
      have hle : (S.L : ℝ) ^ (2 * (S.toDomSeq).sc x) ≤ (S.L : ℝ) ^ 4 * ((S.L : ℝ) ^ (q.1 : ℕ)) ^ 2 := by
        rw [← pow_mul, ← pow_add]; exact pow_le_pow_right₀ hL1 (by omega)
      have hp1 : (0 : ℝ) < ((S.L : ℝ) ^ (q.1 : ℕ)) ^ 2 := by positivity
      have hp2 : (0 : ℝ) < (S.L : ℝ) ^ (2 * (S.toDomSeq).sc x) := by positivity
      rw [inv_pow, ← div_eq_mul_inv, inv_le_iff_one_le_mul₀ hp1, div_mul_eq_mul_div, le_div_iff₀ hp2, one_mul]
      linarith
    have hC := Cpu_nonneg S.L
    have habs : |hL S hM hR q x' - hL S hM hR q x| ≤ Cpu S.L / ((S.L : ℝ) ^ S.mM * (S.L : ℝ) ^ (q.1 : ℕ)) :=
      hlip.trans (by
        have : 0 ≤ Cpu S.L / ((S.L : ℝ) ^ S.mM * (S.L : ℝ) ^ (q.1 : ℕ)) := by positivity
        nlinarith)
    have hsq := pow_le_pow_left₀ (abs_nonneg _) habs 2
    rw [sq_abs] at hsq
    refine hsq.trans ?_
    rw [div_pow, mul_pow]
    calc Cpu S.L ^ 2 / (((S.L : ℝ) ^ S.mM) ^ 2 * ((S.L : ℝ) ^ (q.1 : ℕ)) ^ 2)
        = Cpu S.L ^ 2 / ((S.L : ℝ) ^ S.mM) ^ 2 * ((S.L : ℝ) ^ (q.1 : ℕ))⁻¹ ^ 2 := by field_simp
      _ ≤ Cpu S.L ^ 2 / ((S.L : ℝ) ^ S.mM) ^ 2 * ((S.L : ℝ) ^ 4 * ((S.L : ℝ) ^ (2 * (S.toDomSeq).sc x))⁻¹) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = _ := by ring
  -- the sum over `T1 ∪ T2`
  have hzero : ∀ q, q ∉ T1 ∪ T2 → (hL S hM hR q x' - hL S hM hR q x) ^ 2 = 0 := by
    intro q hq
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_not, T1, T2] at hq
    rw [hq.1, hq.2]; ring
  rw [← Finset.sum_subset (Finset.subset_univ (T1 ∪ T2)) (fun q _ hq => hzero q hq)]
  have hcard : ((T1 ∪ T2).card : ℝ) ≤ 96 := by
    have := Finset.card_union_le T1 T2
    have h1 : T1.card ≤ 48 := card_hL S hM hR x
    have h2 : T2.card ≤ 48 := card_hL S hM hR x'
    exact_mod_cast (this.trans (by omega))
  calc ∑ q ∈ T1 ∪ T2, (hL S hM hR q x' - hL S hM hR q x) ^ 2
      ≤ ∑ _q ∈ T1 ∪ T2, Cpu S.L ^ 2 * (S.L : ℝ) ^ 4 / ((S.L : ℝ) ^ S.mM) ^ 2 * ((S.L : ℝ) ^ (2 * (S.toDomSeq).sc x))⁻¹ :=
        Finset.sum_le_sum hterm
    _ = (T1 ∪ T2).card * (Cpu S.L ^ 2 * (S.L : ℝ) ^ 4 / ((S.L : ℝ) ^ S.mM) ^ 2 *
          ((S.L : ℝ) ^ (2 * (S.toDomSeq).sc x))⁻¹) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 96 * (Cpu S.L ^ 2 * (S.L : ℝ) ^ 4 / ((S.L : ℝ) ^ S.mM) ^ 2 * ((S.L : ℝ) ^ (2 * (S.toDomSeq).sc x))⁻¹) :=
        mul_le_mul_of_nonneg_right hcard (by have := Cpu_nonneg S.L; positivity)
    _ = _ := by ring

end PartitionUnity

namespace PartitionUnity

open Lattices SFBounds SFLocal

variable (S : Lattices.SeqDom) (hM : 12 ≤ S.L ^ S.mM) (hR : 12 * S.L ≤ S.R) {N : ℕ}

local notation "NF" => SequenceAverages.N0 S
local notation "Mat" => Matrix (Fin N) (Fin N) ℂ

/-- **The error of the localisation of `‖∇A‖²`**: `|err_grad| ≤ 384C_pu²L⁶M^{-2}‖A‖_w²`. -/
theorem err_grad_le (hRM : (S.L : ℝ) < ((S.R * S.L ^ S.mM : ℕ) : ℝ)) (A : Fin 4 → Site NF → Mat) :
    |∑ μ, ∑ x, ∑ ν, (∑ q, (hL S hM hR q (x + CoreLean.unit NF ν) - hL S hM hR q x) ^ 2) *
        (inner ℂ (emb (N := N) (A μ (x + CoreLean.unit NF ν))) (emb (A μ x))).re| ≤
      384 * Cpu S.L ^ 2 * (S.L : ℝ) ^ 6 / ((S.L : ℝ) ^ S.mM) ^ 2 * wnorm S A := by
  set K := 96 * Cpu S.L ^ 2 * (S.L : ℝ) ^ 4 / ((S.L : ℝ) ^ S.mM) ^ 2
  have hK : 0 ≤ K := by have := Cpu_nonneg S.L; positivity
  have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast S.Lpos
  set w : Site NF → ℝ := fun x => ((S.L : ℝ) ^ (2 * (S.toDomSeq).sc x))⁻¹
  have hw0 : ∀ x, 0 ≤ w x := fun x => by positivity
  set a : Fin 4 → Site NF → VS N 1 := fun μ x => emb (A μ x)
  -- each term
  have hterm : ∀ μ x ν, |(∑ q, (hL S hM hR q (x + CoreLean.unit NF ν) - hL S hM hR q x) ^ 2) *
      (inner ℂ (a μ (x + CoreLean.unit NF ν)) (a μ x)).re| ≤
      K * (1 / 2) * ((S.L : ℝ) ^ 2 * (w (x + CoreLean.unit NF ν) * ‖a μ (x + CoreLean.unit NF ν)‖ ^ 2) +
        w x * ‖a μ x‖ ^ 2) := by
    intro μ x ν
    have hW := sum_hL_diff_sq S hM hR hRM x ν
    have hW0 : 0 ≤ ∑ q, (hL S hM hR q (x + CoreLean.unit NF ν) - hL S hM hR q x) ^ 2 :=
      Finset.sum_nonneg fun q _ => sq_nonneg _
    have hin : |(inner ℂ (a μ (x + CoreLean.unit NF ν)) (a μ x)).re| ≤
        1 / 2 * (‖a μ (x + CoreLean.unit NF ν)‖ ^ 2 + ‖a μ x‖ ^ 2) := by
      refine (Complex.abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans ?_)
      nlinarith [sq_nonneg (‖a μ (x + CoreLean.unit NF ν)‖ - ‖a μ x‖)]
    have hsc := (sc_unit S hRM x ν).1
    have hww : w x ≤ (S.L : ℝ) ^ 2 * w (x + CoreLean.unit NF ν) := by
      have hp : (S.L : ℝ) ^ (2 * (S.toDomSeq).sc (x + CoreLean.unit NF ν)) ≤
          (S.L : ℝ) ^ 2 * (S.L : ℝ) ^ (2 * (S.toDomSeq).sc x) := by
        rw [← pow_add]; exact pow_le_pow_right₀ hL1 (by omega)
      have hq : (0 : ℝ) < (S.L : ℝ) ^ (2 * (S.toDomSeq).sc (x + CoreLean.unit NF ν)) := by positivity
      have hq' : (0 : ℝ) < (S.L : ℝ) ^ (2 * (S.toDomSeq).sc x) := by positivity
      simp only [w]
      calc ((S.L : ℝ) ^ (2 * (S.toDomSeq).sc x))⁻¹
          = (S.L : ℝ) ^ 2 / ((S.L : ℝ) ^ 2 * (S.L : ℝ) ^ (2 * (S.toDomSeq).sc x)) := by
            field_simp
        _ ≤ (S.L : ℝ) ^ 2 / (S.L : ℝ) ^ (2 * (S.toDomSeq).sc (x + CoreLean.unit NF ν)) :=
            div_le_div_of_nonneg_left (by positivity) hq hp
        _ = _ := div_eq_mul_inv _ _
    rw [abs_mul, abs_of_nonneg hW0]
    calc (∑ q, (hL S hM hR q (x + CoreLean.unit NF ν) - hL S hM hR q x) ^ 2) *
          |(inner ℂ (a μ (x + CoreLean.unit NF ν)) (a μ x)).re|
        ≤ (K * w x) * (1 / 2 * (‖a μ (x + CoreLean.unit NF ν)‖ ^ 2 + ‖a μ x‖ ^ 2)) :=
          mul_le_mul hW hin (abs_nonneg _) (by have := hw0 x; positivity)
      _ ≤ K * (1 / 2) * ((S.L : ℝ) ^ 2 * (w (x + CoreLean.unit NF ν) * ‖a μ (x + CoreLean.unit NF ν)‖ ^ 2) +
          w x * ‖a μ x‖ ^ 2) := by
          have h1 : w x * ‖a μ (x + CoreLean.unit NF ν)‖ ^ 2 ≤
              (S.L : ℝ) ^ 2 * (w (x + CoreLean.unit NF ν) * ‖a μ (x + CoreLean.unit NF ν)‖ ^ 2) := by
            rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hww (sq_nonneg _)
          nlinarith [mul_le_mul_of_nonneg_left h1 hK]
  -- the sum
  have hshift : ∀ μ ν, ∑ x, w (x + CoreLean.unit NF ν) * ‖a μ (x + CoreLean.unit NF ν)‖ ^ 2 =
      ∑ x, w x * ‖a μ x‖ ^ 2 := fun μ ν => sum_shift_site S (fun x => w x * ‖a μ x‖ ^ 2) _
  have hwn : wnorm S A = ∑ μ, ∑ x, w x * ‖a μ x‖ ^ 2 := by
    unfold wnorm
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun x _ => ?_
    simp only [w, a]
    push_cast; rw [← pow_mul, mul_comm 2]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ μ, |∑ x, ∑ ν, (∑ q, (hL S hM hR q (x + CoreLean.unit NF ν) - hL S hM hR q x) ^ 2) *
        (inner ℂ (emb (N := N) (A μ (x + CoreLean.unit NF ν))) (emb (A μ x))).re|
      ≤ ∑ μ, ∑ x, ∑ ν, K * (1 / 2) * ((S.L : ℝ) ^ 2 * (w (x + CoreLean.unit NF ν) * ‖a μ (x + CoreLean.unit NF ν)‖ ^ 2) +
          w x * ‖a μ x‖ ^ 2) := by
        refine Finset.sum_le_sum fun μ _ => (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ =>
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ν _ => hterm μ x ν))
    _ = ∑ μ, K * (1 / 2) * ∑ ν, ((S.L : ℝ) ^ 2 * ∑ x, w x * ‖a μ x‖ ^ 2 + ∑ x, w x * ‖a μ x‖ ^ 2) := by
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun ν _ => ?_
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, hshift]
    _ = 4 * K * (1 / 2) * ((S.L : ℝ) ^ 2 + 1) * ∑ μ, ∑ x, w x * ‖a μ x‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun μ _ => ?_
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring
    _ ≤ 384 * Cpu S.L ^ 2 * (S.L : ℝ) ^ 6 / ((S.L : ℝ) ^ S.mM) ^ 2 * wnorm S A := by
        rw [hwn]
        have hS : 0 ≤ ∑ μ, ∑ x, w x * ‖a μ x‖ ^ 2 :=
          Finset.sum_nonneg fun μ _ => Finset.sum_nonneg fun x _ => mul_nonneg (hw0 x) (sq_nonneg _)
        have hL2 : (S.L : ℝ) ^ 2 + 1 ≤ 2 * (S.L : ℝ) ^ 2 := by nlinarith
        have e : 384 * Cpu S.L ^ 2 * (S.L : ℝ) ^ 6 / ((S.L : ℝ) ^ S.mM) ^ 2 = 4 * K * (1 / 2) * (2 * (S.L : ℝ) ^ 2) := by
          simp only [K]; ring
        rw [e]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL2 (by positivity)) hS

end PartitionUnity

end CoreLean

end
