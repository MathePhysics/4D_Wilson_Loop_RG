/-
`lem:sf-vector-decay` of BALABAN_CORE.tex (`bb3c43c53e37`), step (2) of "The complex field": the term `Δ'(𝐔)` of
`Δ_𝖺(𝐔)` on the fine lattice (`a₀ = 1`).

* `cfgX_move`: `e^{iX} = e^{iX}·id`; `plaq_cfgX`: the plaquettes of `𝐔 = e^{iX}` satisfy
  `|𝐔(∂p) - 1| ≤ 10α₁a_i^{-2}`, `i` the smallest scale of the corners (`cor:moved-plaquette` for the trivial field).
-/
import CoreLean.SFLapComp
import CoreLean.SmallPlaquettes
import CoreLean.HessianBound

open Finset Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFBox SFBox.SeqDomBox SmallFieldDecay SmallFieldCoercivity
  SequenceOperators CompressedInverse SFLocal ConcretePairing LatticeKappa MovedPlaquette SmallPlaquettes

variable (S : SeqDom) {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ
local notation "NF" => SequenceAverages.N0 S
local notation "RMS" => ((S.R * S.L ^ S.mM : ℕ) : ℝ)
set_option quotPrecheck false in
local notation "jj" => (S.toDomSeq).sc

omit S in
lemma cfgX_move {n : ℕ} [NeZero n] (X : Fin 4 → Site n → Mat) : cfgX X = move (triv : Config N n) X 1 := by
  funext ρ z
  simp [cfgX, move, triv]

/-- **The plaquettes of `𝐔 = e^{iX}`** (`cor:moved-plaquette` for the trivial field, `a = a_i`, `ρ = α₁`): if the
four corners of `p = p_{μν}(y)` lie in `Ω_i`, then `|𝐔(∂p) - 1| ≤ 10α₁a_i^{-2}`. -/
lemma plaq_cfgX (G : GaugeGroup N) (hN : 1 ≤ N) {X : Fin 4 → Site NF → Mat} {α₁ : ℝ} (hX : RegField S X α₁)
    (hα0 : 0 ≤ α₁) (hα : α₁ ≤ 1 / 512) (μ ν : Fin 4) (y : Site NF) (i : ℕ)
    (h1 : y ∈ (S.toDomSeq).Ω i) (h2 : y + unit NF μ ∈ (S.toDomSeq).Ω i) (h3 : y + unit NF ν ∈ (S.toDomSeq).Ω i)
    (h4 : y + unit NF μ + unit NF ν ∈ (S.toDomSeq).Ω i) :
    ‖((plaq (cfgX X) μ ν y : GLN) : Mat) - 1‖ ≤ 10 * α₁ * (((S.L : ℝ) ^ i)⁻¹) ^ 2 := by
  have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast S.Lpos
  have hLi : (0 : ℝ) < (S.L : ℝ) ^ i := by positivity
  have hLi1 : (1 : ℝ) ≤ (S.L : ℝ) ^ i := one_le_pow₀ hL1
  have h4' : y + unit NF ν + unit NF μ ∈ (S.toDomSeq).Ω i := by rwa [add_right_comm]
  have htrivG : IsGField G (triv : Config N NF) := fun _ _ => G.carrier.one_mem
  have hAi : ∀ z ρ, z ∈ (S.toDomSeq).Ω i → z + unit NF ρ ∈ (S.toDomSeq).Ω i → (S.L : ℝ) ^ i * ‖X ρ z‖ ≤ α₁ := by
    intro z ρ hz hz'
    have h := hX.hA i z ρ hz hz'
    calc (S.L : ℝ) ^ i * ‖X ρ z‖ ≤ (S.L : ℝ) ^ i * (α₁ * ((S.L : ℝ) ^ i)⁻¹) := mul_le_mul_of_nonneg_left h hLi.le
      _ = α₁ := by field_simp
  have hDi : ∀ z ρ σ, z ∈ (S.toDomSeq).Ω i → z + unit NF σ ∈ (S.toDomSeq).Ω i →
      ((S.L : ℝ) ^ i) ^ 2 * ‖Dcov (triv : Config N NF) X 1 σ ρ z‖ ≤ α₁ := by
    intro z ρ σ hz hz'
    have e : Dcov (triv : Config N NF) X 1 σ ρ z = X ρ (z + unit NF σ) - X ρ z := by
      simp [Dcov, triv, Ad_one']
    rw [e]
    have h := hX.hdA i z ρ σ hz hz'
    calc ((S.L : ℝ) ^ i) ^ 2 * ‖X ρ (z + unit NF σ) - X ρ z‖
        ≤ ((S.L : ℝ) ^ i) ^ 2 * (α₁ * ((S.L : ℝ) ^ (2 * i))⁻¹) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = α₁ := by rw [show (S.L : ℝ) ^ (2 * i) = ((S.L : ℝ) ^ i) ^ 2 by ring]; field_simp
  have hP : hs (((plaq (triv : Config N NF) μ ν y : GLN) : Mat) - 1) ≤ 0 * (1 / (S.L : ℝ) ^ i) ^ 2 := by
    rw [plaq_triv]; simp [RegularAverages.hs_zero']
  have h := (moved_plaquette G hN triv htrivG X μ ν y (η := 1) (a := (S.L : ℝ) ^ i) (ρ := α₁) (α₀ := 0)
    one_pos hLi1 le_rfl hα0 hP (hAi y μ h1 h2) (hAi _ ν h2 h4) (hAi _ μ h3 h4') (hAi y ν h1 h3)
    (hDi y ν μ h1 h2) (hDi y μ ν h1 h3) (by simp) hα).2
  rw [plaq_triv, ← cfgX_move] at h
  simpa [one_div] using h

/-! ### The neighbourhood of a bond -/

omit S in
/-- `-e`, `0`, `e`. -/
def sgnv {n : ℕ} (s : Fin 3) (e : Site n) : Site n := if s = 0 then -e else if s = 1 then 0 else e

/-- The sites `x + s e_a + t e_b`, `s, t ∈ {-1, 0, 1}`. -/
def nbz (x : Site NF) (a b : Fin 4) (s t : Fin 3) : Site NF := x + sgnv s (unit NF a) + sgnv t (unit NF b)

/-- `|φ(x + e_ν) - φ(x)| ≤ 1/16` for `16Lδ ≤ 1`. -/
lemma phi_bond_le {δ : ℝ} (hδ : 0 ≤ δ) (hδL : 16 * S.L * δ ≤ 1) (ph : Site NF → ℝ)
    (hph : ∀ x x', |ph x - ph x'| ≤ δ * S.dF x x') (ν : Fin 4) (x : Site NF) :
    |ph (x + unit NF ν) - ph x| ≤ 1 / 16 := by
  have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast S.Lpos
  have hRM1 : 1 ≤ S.R * S.L ^ S.mM := Nat.one_le_iff_ne_zero.2 (by have := S.one_le_R; have := S.Lpos; positivity)
  have h1 := hph (x + unit NF ν) x
  have h2 := (S.wdist_unit_le_sc hRM1 x ν).2
  rw [S.dF_comm] at h1
  have hr : ((S.L : ℝ) ^ (S.toDomSeq).sc (x + unit NF ν))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hL1)
  calc |ph (x + unit NF ν) - ph x| ≤ δ * S.dF x (x + unit NF ν) := h1
    _ ≤ δ * (S.L * ((S.L : ℝ) ^ (S.toDomSeq).sc (x + unit NF ν))⁻¹) := mul_le_mul_of_nonneg_left h2 hδ
    _ ≤ δ * (S.L * 1) := by gcongr
    _ ≤ 1 / 16 := by nlinarith

/-- **One step**: the scales of `w` and `w ± e_a` differ by at most one, and so do the weights by `1/16`. -/
lemma step_le (hRML : (S.L : ℝ) < RMS) {δ : ℝ} (hδ : 0 ≤ δ) (hδL : 16 * S.L * δ ≤ 1) (ph : Site NF → ℝ)
    (hph : ∀ x x', |ph x - ph x'| ≤ δ * S.dF x x') (w : Site NF) (a : Fin 4) (s : Fin 3) :
    jj w ≤ jj (w + sgnv s (unit NF a)) + 1 ∧ jj (w + sgnv s (unit NF a)) ≤ jj w + 1 ∧
      |ph (w + sgnv s (unit NF a)) - ph w| ≤ 1 / 16 := by
  unfold sgnv
  split_ifs with h0 h1
  · have hu := PartitionUnity.sc_unit S hRML (w + -unit NF a) a
    have hp := phi_bond_le S hδ hδL ph hph a (w + -unit NF a)
    rw [neg_add_cancel_right] at hu hp
    refine ⟨hu.1, hu.2, ?_⟩
    rw [abs_sub_comm]; exact hp
  · simp
  · have hu := PartitionUnity.sc_unit S hRML w a
    exact ⟨hu.2, hu.1, phi_bond_le S hδ hδL ph hph a w⟩

/-- **Two steps**: `|j(x) - j(z)| ≤ 2` and `|φ(z) - φ(x)| ≤ 1/8` for `z = x + s e_a + t e_b`. -/
lemma nbz_le (hRML : (S.L : ℝ) < RMS) {δ : ℝ} (hδ : 0 ≤ δ) (hδL : 16 * S.L * δ ≤ 1) (ph : Site NF → ℝ)
    (hph : ∀ x x', |ph x - ph x'| ≤ δ * S.dF x x') (x : Site NF) (a b : Fin 4) (s t : Fin 3) :
    jj x ≤ jj (nbz S x a b s t) + 2 ∧ jj (nbz S x a b s t) ≤ jj x + 2 ∧ |ph (nbz S x a b s t) - ph x| ≤ 1 / 8 := by
  obtain ⟨h1, h2, h3⟩ := step_le S hRML hδ hδL ph hph x a s
  obtain ⟨h4, h5, h6⟩ := step_le S hRML hδ hδL ph hph (x + sgnv s (unit NF a)) b t
  refine ⟨by unfold nbz; omega, by unfold nbz; omega, ?_⟩
  unfold nbz
  calc |ph (x + sgnv s (unit NF a) + sgnv t (unit NF b)) - ph x|
      = |(ph (x + sgnv s (unit NF a) + sgnv t (unit NF b)) - ph (x + sgnv s (unit NF a))) +
          (ph (x + sgnv s (unit NF a)) - ph x)| := by ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (by linarith)

/-- `Σ_x f(x + s e_a + t e_b) = Σ_x f(x)`. -/
lemma sum_nbz {β : Type*} [AddCommMonoid β] (f : Site NF → β) (a b : Fin 4) (s t : Fin 3) :
    ∑ x, f (nbz S x a b s t) = ∑ x, f x := by
  unfold nbz
  simp only [add_assoc]
  exact sum_shift_site S f _

/-- The sites of the plaquettes through the bond `(x, x + e_μ)`: if `p_{μ'ν'}(y)` contains it, then the corners of
`p` are of the form `x + s e_a + t e_b`. -/
lemma corners_nbz {μ' ν' : Fin 4} {y : Site NF} {μ : Fin 4} {x : Site NF} (h : Contains μ' ν' y μ x) :
    (∃ a b s t, y = nbz S x a b s t) ∧ (∃ a b s t, y + unit NF μ' = nbz S x a b s t) ∧
      (∃ a b s t, y + unit NF ν' = nbz S x a b s t) ∧
        (∃ a b s t, y + unit NF μ' + unit NF ν' = nbz S x a b s t) := by
  have hy : y = x ∨ y = x - unit NF ν' ∨ y = x - unit NF μ' := by
    rcases h with ⟨_, rfl | hy⟩ | ⟨_, hy | rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (eq_sub_of_add_eq hy))
    · exact Or.inr (Or.inr (eq_sub_of_add_eq hy))
    · exact Or.inl rfl
  rcases hy with rfl | rfl | rfl
  · refine ⟨⟨0, 0, 1, 1, ?_⟩, ⟨μ', 0, 2, 1, ?_⟩, ⟨ν', 0, 2, 1, ?_⟩, ⟨μ', ν', 2, 2, ?_⟩⟩ <;>
      simp [nbz, sgnv]
  · refine ⟨⟨ν', 0, 0, 1, ?_⟩, ⟨ν', μ', 0, 2, ?_⟩, ⟨0, 0, 1, 1, ?_⟩, ⟨μ', 0, 2, 1, ?_⟩⟩ <;>
      simp [nbz, sgnv] <;> abel
  · refine ⟨⟨μ', 0, 0, 1, ?_⟩, ⟨0, 0, 1, 1, ?_⟩, ⟨μ', ν', 0, 2, ?_⟩, ⟨ν', 0, 2, 1, ?_⟩⟩ <;>
      simp [nbz, sgnv] <;> abel

/-! ### The bound of `Δ'(𝐔)` at a bond -/

lemma one_lt_NF : 1 < NF := by
  rw [SequenceAverages.N0_eq]
  have : 1 ≤ S.L ^ (S.mT + S.k) := Nat.one_le_pow _ _ S.Lpos
  omega

/-- The sum of `|C|` over the bonds based in the neighbourhood of `x`. -/
def m0 (C : Fin 4 → Site NF → Mat) (x : Site NF) : ℝ :=
  ∑ ρ, ∑ a, ∑ b, ∑ s, ∑ t, ‖C ρ (nbz S x a b s t)‖

lemma le_m0 (C : Fin 4 → Site NF → Mat) (x : Site NF) (ρ a b : Fin 4) (s t : Fin 3) :
    ‖C ρ (nbz S x a b s t)‖ ≤ m0 S C x := by
  unfold m0
  calc ‖C ρ (nbz S x a b s t)‖ ≤ ∑ t', ‖C ρ (nbz S x a b s t')‖ :=
        single_le_sum (f := fun t' => ‖C ρ (nbz S x a b s t')‖) (fun _ _ => norm_nonneg _) (mem_univ t)
    _ ≤ ∑ s', ∑ t', ‖C ρ (nbz S x a b s' t')‖ :=
        single_le_sum (f := fun s' => ∑ t', ‖C ρ (nbz S x a b s' t')‖)
          (fun _ _ => sum_nonneg fun _ _ => norm_nonneg _) (mem_univ s)
    _ ≤ ∑ b', ∑ s', ∑ t', ‖C ρ (nbz S x a b' s' t')‖ :=
        single_le_sum (f := fun b' => ∑ s', ∑ t', ‖C ρ (nbz S x a b' s' t')‖)
          (fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => norm_nonneg _) (mem_univ b)
    _ ≤ ∑ a', ∑ b', ∑ s', ∑ t', ‖C ρ (nbz S x a' b' s' t')‖ :=
        single_le_sum (f := fun a' => ∑ b', ∑ s', ∑ t', ‖C ρ (nbz S x a' b' s' t')‖)
          (fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => norm_nonneg _) (mem_univ a)
    _ ≤ _ :=
        single_le_sum (f := fun ρ' => ∑ a', ∑ b', ∑ s', ∑ t', ‖C ρ' (nbz S x a' b' s' t')‖)
          (fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ =>
            norm_nonneg _) (mem_univ ρ)

/-- **`lem:hessian`(ii) at `𝐔 = e^{iX}`**: `|(Δ'(𝐔)C)(x, x + e_μ)| ≤ 252N^{3/2}·10α₁L⁴a_{j(x)}^{-2}m₀(C, x)`, with the
plaquettes of `plaq_cfgX` on `Ω_{j(x)-2}` and the transports of `small_Ad`. -/
theorem hess_bond_le {G : GaugeGroup N} (hG : G.LieInput) [NeZero N] (hRML : (S.L : ℝ) < RMS)
    {X : Fin 4 → Site NF → Mat} {α₁ : ℝ} (hX : RegField S X α₁) (hα0 : 0 ≤ α₁) (hα : α₁ ≤ 1 / 512)
    (C : Fin 4 → Site NF → Mat) (μ : Fin 4) (x : Site NF) :
    ‖hessOp' a1 hG (cfgX X) C μ x‖ ≤
      252 * ((N : ℝ) * √N) * (10 * α₁ * (S.L : ℝ) ^ 4 * (((S.L : ℝ) ^ jj x)⁻¹) ^ 2) * m0 S C x := by
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast S.Lpos
  have ha : a1 ≠ 0 := by simp [a1]
  set i := jj x - 2
  have hscale : ∀ z, jj x ≤ jj z + 2 → z ∈ (S.toDomSeq).Ω i := fun z hz =>
    S.toDomSeq.Ω_anti (show i ≤ jj z by simp only [i]; omega) (S.toDomSeq.mem_sc z)
  have hcorner : ∀ z, (∃ a b s t, z = nbz S x a b s t) → z ∈ (S.toDomSeq).Ω i := by
    rintro z ⟨a, b, s, t, rfl⟩
    -- the scale bound needs only `sc_unit`; the weight is not used
    have h := nbz_le S hRML le_rfl (by simp) (fun _ => (0 : ℝ)) (fun _ _ => by simp) x a b s t
    exact hscale _ h.1
  have hLi : ((S.L : ℝ) ^ i)⁻¹ ≤ (S.L : ℝ) ^ 2 * ((S.L : ℝ) ^ jj x)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), ← div_eq_inv_mul, div_le_iff₀ (by positivity)]
    rw [← pow_add]
    exact pow_le_pow_right₀ hL1 (by simp only [i]; omega)
  have hLi1 : ((S.L : ℝ) ^ i)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hL1)
  have hP : ∀ μ' ν' y, μ' < ν' → Contains μ' ν' y μ x →
      ‖((plaq (cfgX X) μ' ν' y : GLN) : Mat) - 1‖ ≤ 1 / 2 ∧
        hs (((plaq (cfgX X) μ' ν' y : GLN) : Mat) - 1) ≤ 10 * α₁ * (S.L : ℝ) ^ 4 * (((S.L : ℝ) ^ jj x)⁻¹) ^ 2 := by
    intro μ' ν' y _ hc
    obtain ⟨c1, c2, c3, c4⟩ := corners_nbz S hc
    have hp := plaq_cfgX S G hN hX hα0 hα μ' ν' y i (hcorner _ c1) (hcorner _ c2) (hcorner _ c3) (hcorner _ c4)
    have hq : ((S.L : ℝ) ^ i)⁻¹ ^ 2 ≤ 1 := pow_le_one₀ (by positivity) hLi1
    refine ⟨hp.trans (by nlinarith), (hs_le_opNorm (Nat.pos_of_ne_zero (NeZero.ne N)) _).trans (hp.trans ?_)⟩
    have h2 : ((S.L : ℝ) ^ i)⁻¹ ^ 2 ≤ ((S.L : ℝ) ^ 2 * ((S.L : ℝ) ^ jj x)⁻¹) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hLi 2
    calc 10 * α₁ * ((S.L : ℝ) ^ i)⁻¹ ^ 2 ≤ 10 * α₁ * ((S.L : ℝ) ^ 2 * ((S.L : ℝ) ^ jj x)⁻¹) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by ring
  have htrivG : IsGField G (triv : Config N NF) := fun _ _ => G.carrier.one_mem
  have hAd : ∀ μ' ν' y, μ' < ν' → Contains μ' ν' y μ x →
      ∀ Z : Mat, ‖Ad (cfgX X μ' y) Z‖ ≤ 2 * ‖Z‖ ∧ ‖Ad (cfgX X ν' y) Z‖ ≤ 2 * ‖Z‖ := by
    intro μ' ν' y _ _ Z
    have he : Real.exp (2 * α₁) ≤ 2 := by
      calc Real.exp (2 * α₁) ≤ Real.exp (Real.log 2) :=
            Real.exp_le_exp.2 (by have := Real.log_two_gt_d9; linarith)
        _ = 2 := Real.exp_log (by norm_num)
    have hb : ∀ ρ, ‖Ad (cfgX X ρ y) Z‖ ≤ 2 * ‖Z‖ := fun ρ => by
      have h := (small_Ad G triv htrivG X ρ y (α₁ := α₁) zero_le_one (by simpa using X_le_one S hX hα0 ρ y) Z).1
      rw [← cfgX_move] at h
      exact h.trans (mul_le_mul_of_nonneg_right he (norm_nonneg _))
    exact ⟨hb μ', hb ν'⟩
  have hA : ∀ μ' ν' y, μ' < ν' → Contains μ' ν' y μ x →
      ‖C μ' y‖ ≤ m0 S C x ∧ ‖C ν' (y + unit NF μ')‖ ≤ m0 S C x ∧ ‖C μ' (y + unit NF ν')‖ ≤ m0 S C x ∧
        ‖C ν' y‖ ≤ m0 S C x := by
    intro μ' ν' y _ hc
    obtain ⟨⟨a1', b1, s1, t1, e1⟩, ⟨a2, b2, s2, t2, e2⟩, ⟨a3, b3, s3, t3, e3⟩, _⟩ := corners_nbz S hc
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [e1]; exact le_m0 S C x _ _ _ _ _
    · rw [e2]; exact le_m0 S C x _ _ _ _ _
    · rw [e3]; exact le_m0 S C x _ _ _ _ _
    · rw [e1]; exact le_m0 S C x _ _ _ _ _
  have h := norm_hessOp'_le a1 hG ha (one_lt_NF S) (cfgX X) C μ x hP hAd hA
  have hna : ‖a1‖ = 1 := by simp [a1]
  rw [hna, one_pow, inv_one, mul_one] at h
  exact h

/-! ### The form of `Δ'(𝐔)` -/

/-- **The term `Δ'(𝐔)`** (step (2) of "The complex field"):
`|⟨(e^φA)^*, Δ'(𝐔)(e^{-φ}A)⟩| ≤ 2903040N²α₁L⁶‖A‖_w²`. -/
theorem hess_comp {G : GaugeGroup N} (hG : G.LieInput) [NeZero N] (hRML : (S.L : ℝ) < RMS)
    {X : Fin 4 → Site NF → Mat} {α₁ : ℝ} (hX : RegField S X α₁) (hα0 : 0 ≤ α₁) (hα : α₁ ≤ 1 / 512)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδL : 16 * S.L * δ ≤ 1) (ph : Site NF → ℝ)
    (hph : ∀ x x', |ph x - ph x'| ≤ δ * S.dF x x') (A : Fin 4 → Site NF → Mat) :
    ‖pair1V S (expA S ph A) (hessOp' a1 hG (cfgX X) (expA S (fun x => -ph x) A))‖ ≤
      2903040 * (N : ℝ) ^ 2 * α₁ * (S.L : ℝ) ^ 6 * wnorm S A := by
  have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast S.Lpos
  have hL0 : (0 : ℝ) ≤ S.L := by linarith
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hsN := Real.sqrt_nonneg (N : ℝ)
  have hsN2 : √(N : ℝ) * √(N : ℝ) = N := Real.mul_self_sqrt (Nat.cast_nonneg _)
  set C := expA S (fun x => -ph x) A
  set r : Site NF → ℝ := fun y => ((S.L : ℝ) ^ jj y)⁻¹
  set u : Fin 4 → Site NF → ℝ := fun μ y => r y * hs (A μ y)
  have hu0 : ∀ μ y, 0 ≤ u μ y := fun μ y => mul_nonneg (by positivity) (hs_nonneg _)
  set K1 := 5040 * (N : ℝ) ^ 3 * α₁ * (S.L : ℝ) ^ 6
  have hK1 : 0 ≤ K1 := by positivity
  -- a term
  have hpt : ∀ μ x, ‖inner ℂ (emb (N := N) (expA S ph A μ x)) (emb (N := N) (hessOp' a1 hG (cfgX X) C μ x))‖ ≤
      K1 * ∑ ρ, ∑ a, ∑ b, ∑ s, ∑ t, u μ x * u ρ (nbz S x a b s t) := by
    intro μ x
    refine (norm_inner_le_norm _ _).trans ?_
    rw [norm_emb, norm_emb]
    have hB : hs (expA S ph A μ x) = Real.exp (ph x) * hs (A μ x) := by
      simp only [expA]
      rw [RegularAverages.hs_smul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have hH := (hs_le_opNorm hN0 (hessOp' a1 hG (cfgX X) C μ x)).trans
      (hess_bond_le S hG hRML hX hα0 hα C μ x)
    have hm : m0 S C x ≤ ∑ ρ, ∑ a, ∑ b, ∑ s, ∑ t,
        √N * (Real.exp (-ph (nbz S x a b s t)) * hs (A ρ (nbz S x a b s t))) := by
      unfold m0
      refine sum_le_sum fun ρ _ => sum_le_sum fun a _ => sum_le_sum fun b _ => sum_le_sum fun s _ =>
        sum_le_sum fun t _ => ?_
      refine (opNorm_le_sqrt_mul_hs _).trans (le_of_eq ?_)
      simp only [C, expA]
      rw [RegularAverages.hs_smul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have hterm : ∀ ρ a b s t, Real.exp (ph x) * hs (A μ x) * (((S.L : ℝ) ^ jj x)⁻¹ ^ 2 *
        (Real.exp (-ph (nbz S x a b s t)) * hs (A ρ (nbz S x a b s t)))) ≤
        2 * (S.L : ℝ) ^ 2 * (u μ x * u ρ (nbz S x a b s t)) := by
      intro ρ a b s t
      obtain ⟨_, h2, h3⟩ := nbz_le S hRML hδ hδL ph hph x a b s t
      have he : Real.exp (ph x) * Real.exp (-ph (nbz S x a b s t)) ≤ 2 := by
        rw [← Real.exp_add]
        calc Real.exp (ph x + -ph (nbz S x a b s t)) ≤ Real.exp (Real.log 2) := by
              refine Real.exp_le_exp.2 ?_
              have := Real.log_two_gt_d9
              have := neg_abs_le (ph (nbz S x a b s t) - ph x)
              linarith
          _ = 2 := Real.exp_log (by norm_num)
      have hr : ((S.L : ℝ) ^ jj x)⁻¹ ≤ (S.L : ℝ) ^ 2 * r (nbz S x a b s t) := by
        simp only [r]
        rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), ← div_eq_inv_mul, div_le_iff₀ (by positivity)]
        rw [← pow_add]
        exact pow_le_pow_right₀ hL1 (by omega)
      have hA1 := hs_nonneg (N := N) (A μ x)
      have hA2 := hs_nonneg (N := N) (A ρ (nbz S x a b s t))
      have hrx : 0 ≤ ((S.L : ℝ) ^ jj x)⁻¹ := by positivity
      calc Real.exp (ph x) * hs (A μ x) * (((S.L : ℝ) ^ jj x)⁻¹ ^ 2 *
            (Real.exp (-ph (nbz S x a b s t)) * hs (A ρ (nbz S x a b s t))))
          = (Real.exp (ph x) * Real.exp (-ph (nbz S x a b s t))) * (((S.L : ℝ) ^ jj x)⁻¹ * hs (A μ x)) *
              (((S.L : ℝ) ^ jj x)⁻¹ * hs (A ρ (nbz S x a b s t))) := by ring
        _ ≤ 2 * (((S.L : ℝ) ^ jj x)⁻¹ * hs (A μ x)) *
              ((S.L : ℝ) ^ 2 * r (nbz S x a b s t) * hs (A ρ (nbz S x a b s t))) := by gcongr
        _ = _ := by simp only [u, r]; ring
    have hBn : 0 ≤ √N * (Real.exp (ph x) * hs (A μ x)) := mul_nonneg hsN (mul_nonneg (Real.exp_pos _).le (hs_nonneg _))
    calc √N * hs (expA S ph A μ x) * (√N * hs (hessOp' a1 hG (cfgX X) C μ x))
        ≤ √N * (Real.exp (ph x) * hs (A μ x)) * (√N * (252 * ((N : ℝ) * √N) *
            (10 * α₁ * (S.L : ℝ) ^ 4 * (((S.L : ℝ) ^ jj x)⁻¹) ^ 2) * ∑ ρ, ∑ a, ∑ b, ∑ s, ∑ t,
              √N * (Real.exp (-ph (nbz S x a b s t)) * hs (A ρ (nbz S x a b s t))))) := by
          rw [hB]
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hH.trans ?_) hsN) hBn
          exact mul_le_mul_of_nonneg_left hm (by positivity)
      _ = 2520 * ((√N * √N) * (√N * √N)) * ((N : ℝ) * α₁ * (S.L : ℝ) ^ 4) * ∑ ρ, ∑ a, ∑ b, ∑ s, ∑ t,
            Real.exp (ph x) * hs (A μ x) * (((S.L : ℝ) ^ jj x)⁻¹ ^ 2 *
              (Real.exp (-ph (nbz S x a b s t)) * hs (A ρ (nbz S x a b s t)))) := by
          simp only [mul_sum]
          refine sum_congr rfl fun ρ _ => sum_congr rfl fun a _ => sum_congr rfl fun b _ =>
            sum_congr rfl fun s _ => sum_congr rfl fun t _ => ?_
          ring
      _ ≤ 2520 * ((√N * √N) * (√N * √N)) * ((N : ℝ) * α₁ * (S.L : ℝ) ^ 4) * ∑ ρ, ∑ a, ∑ b, ∑ s, ∑ t,
            2 * (S.L : ℝ) ^ 2 * (u μ x * u ρ (nbz S x a b s t)) := by
          refine mul_le_mul_of_nonneg_left (sum_le_sum fun ρ _ => sum_le_sum fun a _ => sum_le_sum fun b _ =>
            sum_le_sum fun s _ => sum_le_sum fun t _ => hterm ρ a b s t) (by positivity)
      _ = _ := by
          rw [hsN2]
          simp only [K1, mul_sum]
          refine sum_congr rfl fun ρ _ => sum_congr rfl fun a _ => sum_congr rfl fun b _ =>
            sum_congr rfl fun s _ => sum_congr rfl fun t _ => ?_
          ring
  -- the sum
  have hwn : wnorm S A = N * ∑ μ, ∑ y, u μ y ^ 2 := by
    unfold wnorm
    simp only [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun μ _ => sum_congr rfl fun y _ => ?_
    rw [norm_emb_sq]
    simp only [u, r]
    push_cast
    rw [mul_pow, inv_pow, hs_sq]
    ring
  have hamgm : ∀ μ x ρ a b s t, u μ x * u ρ (nbz S x a b s t) ≤ (u μ x ^ 2 + u ρ (nbz S x a b s t) ^ 2) / 2 :=
    fun μ x ρ a b s t => by nlinarith [sq_nonneg (u μ x - u ρ (nbz S x a b s t))]
  have hcount1 : ∑ μ, ∑ x, ∑ ρ : Fin 4, ∑ a : Fin 4, ∑ b : Fin 4, ∑ s : Fin 3, ∑ t : Fin 3, u μ x ^ 2 =
      576 * ∑ μ, ∑ y, u μ y ^ 2 := by
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_sum]
    refine sum_congr rfl fun μ _ => sum_congr rfl fun x _ => ?_
    norm_num; ring
  have hcount2 : ∑ μ : Fin 4, ∑ x, ∑ ρ, ∑ a, ∑ b, ∑ s, ∑ t, u ρ (nbz S x a b s t) ^ 2 =
      576 * ∑ μ, ∑ y, u μ y ^ 2 := by
    have e : ∀ ρ a b s t, ∑ x, u ρ (nbz S x a b s t) ^ 2 = ∑ y, u ρ y ^ 2 := fun ρ a b s t =>
      sum_nbz S (fun y => u ρ y ^ 2) a b s t
    have e2 : ∀ μ : Fin 4, ∑ x, ∑ ρ, ∑ a, ∑ b, ∑ s, ∑ t, u ρ (nbz S x a b s t) ^ 2 =
        ∑ ρ, ∑ a : Fin 4, ∑ b : Fin 4, ∑ s : Fin 3, ∑ t : Fin 3, ∑ y, u ρ y ^ 2 := by
      intro μ
      rw [sum_comm]
      refine sum_congr rfl fun ρ _ => ?_
      rw [sum_comm]
      refine sum_congr rfl fun a _ => ?_
      rw [sum_comm]
      refine sum_congr rfl fun b _ => ?_
      rw [sum_comm]
      refine sum_congr rfl fun s _ => ?_
      rw [sum_comm]
      exact sum_congr rfl fun t _ => e ρ a b s t
    rw [sum_congr rfl fun μ _ => e2 μ]
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_sum]
    norm_num
    ring
  calc ‖pair1V S (expA S ph A) (hessOp' a1 hG (cfgX X) C)‖
      ≤ ∑ μ, ∑ x, ‖inner ℂ (emb (N := N) (expA S ph A μ x)) (emb (N := N) (hessOp' a1 hG (cfgX X) C μ x))‖ :=
        (norm_sum_le _ _).trans (sum_le_sum fun μ _ => norm_sum_le _ _)
    _ ≤ ∑ μ, ∑ x, K1 * ∑ ρ, ∑ a, ∑ b, ∑ s, ∑ t, u μ x * u ρ (nbz S x a b s t) :=
        sum_le_sum fun μ _ => sum_le_sum fun x _ => hpt μ x
    _ ≤ ∑ μ, ∑ x, K1 * ∑ ρ, ∑ a, ∑ b, ∑ s, ∑ t, (u μ x ^ 2 + u ρ (nbz S x a b s t) ^ 2) / 2 := by
        refine sum_le_sum fun μ _ => sum_le_sum fun x _ => mul_le_mul_of_nonneg_left ?_ hK1
        exact sum_le_sum fun ρ _ => sum_le_sum fun a _ => sum_le_sum fun b _ => sum_le_sum fun s _ =>
          sum_le_sum fun t _ => hamgm μ x ρ a b s t
    _ = K1 / 2 * (∑ μ, ∑ x, ∑ ρ : Fin 4, ∑ a : Fin 4, ∑ b : Fin 4, ∑ s : Fin 3, ∑ t : Fin 3, u μ x ^ 2 +
          ∑ μ : Fin 4, ∑ x, ∑ ρ, ∑ a, ∑ b, ∑ s, ∑ t, u ρ (nbz S x a b s t) ^ 2) := by
        rw [mul_add, mul_sum, mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun μ _ => ?_
        rw [mul_sum, mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun x _ => ?_
        simp only [mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun ρ _ => sum_congr rfl fun a _ => sum_congr rfl fun b _ =>
          sum_congr rfl fun s _ => sum_congr rfl fun t _ => ?_
        ring
    _ = _ := by
        rw [hcount1, hcount2, hwn]
        simp only [K1]
        field_simp
        ring

end SFBounds
end CoreLean

end
