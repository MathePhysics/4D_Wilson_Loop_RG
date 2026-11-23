/-
**`lem:axial-poincare`** of BALABAN_CORE.tex (`a021c13be348`). `Λ = Π_μ{x⁻_μ, …, x⁺_μ} ⊂ ℤ⁴` with `x⁺_μ - x⁻_μ < ℓ`;
`B` is a real function on the bonds `⟨x, x + e_μ⟩` (`B x μ`) which vanishes on the tree of the axial gauge, the bonds
`⟨x, x + e_μ⟩` with `x_ν = x⁻_ν` for all `ν < μ`. Then `Σ_bB(b)² ≤ 4ℓ⁵Σ_p(∂B)(p)²`, the sums over the bonds and the
plaquettes of `Λ`, `(∂B)(y, ν, μ) = B(y, ν) + B(y + e_ν, μ) - B(y + e_μ, ν) - B(y, μ)`.
The proof is the core's: `B(x, μ)` is the sum of `∂B` over the strips `S_b` of the planes `(ν, μ)`, `ν < μ` (telescoping
in each coordinate `ν < μ`, the bonds of the direction `ν` of the strips being bonds of the tree); Cauchy–Schwarz gives
`B(b)² ≤ 3ℓΣ_{p ∈ S_b}(∂B)(p)²`; and a plaquette lies in at most `ℓ³` strips.
-/
import Mathlib

open Finset

noncomputable section

namespace CoreLean
namespace Axial

/-- The unit vector `e_μ`. -/
abbrev e (μ : Fin 4) : Fin 4 → ℤ := Pi.single μ 1

variable (lo hi : Fin 4 → ℤ)

/-- The box `Λ = Π_μ{x⁻_μ, …, x⁺_μ}`. -/
def box : Finset (Fin 4 → ℤ) := Fintype.piFinset fun i => Finset.Icc (lo i) (hi i)

/-- The bonds of the direction `μ` of `Λ`, by their first ends. -/
def bonds (μ : Fin 4) : Finset (Fin 4 → ℤ) := (box lo hi).filter fun x => x + e μ ∈ box lo hi

/-- The plaquettes of the plane `(ν, μ)` of `Λ`, by their base points. -/
def plaq (ν μ : Fin 4) : Finset (Fin 4 → ℤ) :=
  (box lo hi).filter fun y => y + e ν ∈ box lo hi ∧ y + e μ ∈ box lo hi

/-- `(∂B)(y, ν, μ)`. -/
def dB (B : (Fin 4 → ℤ) → Fin 4 → ℝ) (y : Fin 4 → ℤ) (ν μ : Fin 4) : ℝ :=
  B y ν + B (y + e ν) μ - B (y + e μ) ν - B y μ

/-- The base points of the strip of the plane `(ν, μ)`: coordinates `< ν` at `x⁻`, the coordinate `ν` equal to `s`,
the others those of `x`. -/
def r (ν : Fin 4) (s : ℤ) (x : Fin 4 → ℤ) : Fin 4 → ℤ := fun i => if i < ν then lo i else if i = ν then s else x i

variable {lo hi}

lemma mem_box {x : Fin 4 → ℤ} : x ∈ box lo hi ↔ ∀ i, lo i ≤ x i ∧ x i ≤ hi i := by
  simp [box, Fintype.mem_piFinset]

lemma add_e_apply (y : Fin 4 → ℤ) (μ i : Fin 4) : (y + e μ) i = y i + if i = μ then 1 else 0 := by
  simp [e, Pi.single_apply]

lemma r_add_e_self (ν : Fin 4) (s : ℤ) (x : Fin 4 → ℤ) : r lo ν s x + e ν = r lo ν (s + 1) x := by
  funext i
  rw [add_e_apply]
  unfold r
  by_cases h1 : i < ν
  · simp [h1, h1.ne]
  · by_cases h2 : i = ν
    · subst h2; simp
    · simp [h1, h2]

lemma r_add_e_gt {ν μ : Fin 4} (h : ν < μ) (s : ℤ) (x : Fin 4 → ℤ) : r lo ν s x + e μ = r lo ν s (x + e μ) := by
  funext i
  rw [add_e_apply]
  unfold r
  by_cases h1 : i < ν
  · have : i ≠ μ := ne_of_lt (h1.trans h)
    simp [h1, this]
  · by_cases h2 : i = ν
    · subst h2; simp [h.ne]
    · simp only [h1, h2, if_false]; rw [add_e_apply]

lemma r_mem {ν : Fin 4} {s : ℤ} {x : Fin 4 → ℤ} (hx : x ∈ box lo hi) (hs1 : lo ν ≤ s) (hs2 : s ≤ x ν) :
    r lo ν s x ∈ box lo hi := by
  rw [mem_box] at hx ⊢
  intro i
  unfold r
  by_cases h1 : i < ν
  · simp only [h1, if_true]; exact ⟨le_rfl, (hx i).1.trans (hx i).2⟩
  · by_cases h2 : i = ν
    · subst h2; simp only [lt_irrefl, if_false, if_true]; exact ⟨hs1, hs2.trans (hx _).2⟩
    · simp only [h1, h2, if_false]; exact hx i

/-- **The strip identity**: for a bond `⟨x, x + e_μ⟩` of `Λ` and the tree condition,
`B(x, μ) = Σ_{ν < μ}Σ_{0 ≤ k < x_ν - x⁻_ν}(∂B)(r_ν(x⁻_ν + k, x), ν, μ)`. -/
theorem strip (B : (Fin 4 → ℤ) → Fin 4 → ℝ)
    (htree : ∀ μ x, x ∈ box lo hi → x + e μ ∈ box lo hi → (∀ i < μ, x i = lo i) → B x μ = 0)
    {μ : Fin 4} {x : Fin 4 → ℤ} (hx : x ∈ box lo hi) (hxe : x + e μ ∈ box lo hi) :
    B x μ = ∑ ν ∈ Finset.univ.filter (· < μ), ∑ k ∈ Finset.range (x ν - lo ν).toNat,
      dB B (r lo ν (lo ν + k) x) ν μ := by
  -- the points with the coordinates `< n` at `x⁻`
  set pt : ℕ → Fin 4 → ℤ := fun n i => if (i : ℕ) < n then lo i else x i with hpt
  have hxb := mem_box.1 hx
  have hpt_mem : ∀ n, pt n ∈ box lo hi := fun n => mem_box.2 fun i => by
    simp only [hpt]; split_ifs
    · exact ⟨le_rfl, (hxb i).1.trans (hxb i).2⟩
    · exact hxb i
  have hpte : ∀ n, (n : ℕ) ≤ μ → pt n + e μ ∈ box lo hi := fun n hn => by
    have hxeb := mem_box.1 hxe
    refine mem_box.2 fun i => ?_
    have := hxeb i
    rw [add_e_apply] at this
    rw [add_e_apply]
    by_cases h1 : (i : ℕ) < n
    · simp only [hpt, h1, if_true]
      by_cases hiμ : i = μ
      · subst hiμ; omega
      · simp only [hiμ, if_false, add_zero]; exact ⟨le_rfl, (hxb i).1.trans (hxb i).2⟩
    · simp only [hpt, h1, if_false]; exact this
  -- one coordinate: `B(pt ν, μ) = B(pt (ν+1), μ) + Σ_k ∂B`
  have hstep : ∀ ν : Fin 4, ν < μ → B (pt ν) μ = B (pt (ν + 1)) μ +
      ∑ k ∈ Finset.range (x ν - lo ν).toNat, dB B (r lo ν (lo ν + k) x) ν μ := by
    intro ν hν
    have hlo : lo ν ≤ x ν := (hxb ν).1
    have hr0 : r lo ν (lo ν) x = pt (ν + 1) := by
      funext i; simp only [r, hpt]
      by_cases h1 : i < ν
      · have : (i : ℕ) < ν + 1 := by have := Fin.lt_def.1 h1; omega
        simp [h1, this]
      · by_cases h2 : i = ν
        · subst h2; simp
        · have : ¬ (i : ℕ) < ν + 1 := by
            have h3 : ν < i := lt_of_le_of_ne (not_lt.1 h1) (Ne.symm h2)
            have := Fin.lt_def.1 h3; omega
          simp [h1, h2, this]
    have hrn : r lo ν (x ν) x = pt ν := by
      funext i; simp only [r, hpt]
      by_cases h1 : i < ν
      · simp [h1, Fin.lt_def.1 h1]
      · by_cases h2 : i = ν
        · subst h2; simp
        · simp [h1, h2, show ¬ (i : ℕ) < ν from fun h => h1 (Fin.lt_def.2 h)]
    -- the telescoping in the coordinate `ν`
    have htel : ∀ n : ℕ, n ≤ (x ν - lo ν).toNat → B (r lo ν (lo ν + n) x) μ = B (r lo ν (lo ν) x) μ +
        ∑ k ∈ Finset.range n, dB B (r lo ν (lo ν + k) x) ν μ := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        intro hn
        have hn' : (n : ℤ) + 1 ≤ x ν - lo ν := by
          have := Int.toNat_of_nonneg (sub_nonneg.2 hlo); omega
        rw [Finset.sum_range_succ, ← add_assoc, ← ih (by omega)]
        set y := r lo ν (lo ν + n) x with hy
        have hy_mem : y ∈ box lo hi := r_mem hx (by omega) (by omega)
        have hy1 : y + e ν = r lo ν (lo ν + ↑(n + 1)) x := by
          rw [hy, r_add_e_self]; push_cast; ring_nf
        have hye_mem : y + e ν ∈ box lo hi := by rw [hy1]; exact r_mem hx (by omega) (by push_cast; omega)
        have hyμ : y + e μ = r lo ν (lo ν + n) (x + e μ) := r_add_e_gt hν _ _
        have hxe_ν : (x + e μ) ν = x ν := by rw [add_e_apply]; simp [hν.ne]
        have hyμ_mem : y + e μ ∈ box lo hi := by
          rw [hyμ]; exact r_mem hxe (by omega) (by rw [hxe_ν]; omega)
        have hyμν_mem : y + e μ + e ν ∈ box lo hi := by
          rw [hyμ, r_add_e_self]; exact r_mem hxe (by omega) (by rw [hxe_ν]; omega)
        have hlow : ∀ z : Fin 4 → ℤ, (∀ i < ν, z i = lo i) → True := fun _ _ => trivial
        have hb1 : B y ν = 0 := htree ν y hy_mem hye_mem fun i hi => by simp [hy, r, hi]
        have hb2 : B (y + e μ) ν = 0 := htree ν (y + e μ) hyμ_mem hyμν_mem fun i hi => by
          rw [hyμ]; simp [r, hi]
        unfold dB
        rw [hb1, hb2, ← hy1]; ring
    have := htel _ le_rfl
    rw [show lo ν + ((x ν - lo ν).toNat : ℤ) = x ν by rw [Int.toNat_of_nonneg (sub_nonneg.2 hlo)]; ring,
      hrn, hr0] at this
    exact this
  -- the induction over the coordinates
  have hall : ∀ m : ℕ, m ≤ μ → B (pt (μ - m)) μ = ∑ ν ∈ Finset.univ.filter (fun ν : Fin 4 => μ - m ≤ (ν : ℕ) ∧ ν < μ),
      ∑ k ∈ Finset.range (x ν - lo ν).toNat, dB B (r lo ν (lo ν + k) x) ν μ := by
    intro m
    induction m with
    | zero =>
      intro _
      rw [Nat.sub_zero]
      have h0 : Finset.univ.filter (fun ν : Fin 4 => (μ : ℕ) ≤ ν ∧ ν < μ) = ∅ :=
        Finset.filter_eq_empty_iff.2 fun ν _ h => absurd (Fin.lt_def.1 h.2) (not_lt.2 h.1)
      rw [h0, Finset.sum_empty]
      exact htree μ (pt μ) (hpt_mem _) (hpte _ le_rfl) fun i hi => by simp [hpt, Fin.lt_def.1 hi]
    | succ m ih =>
      intro hm
      set ν : Fin 4 := ⟨μ - (m + 1), by omega⟩ with hνdef
      have hν : ν < μ := Fin.lt_def.2 (by simp [hνdef]; omega)
      have hνs : (ν : ℕ) + 1 = μ - m := by simp [hνdef]; omega
      have h := hstep ν hν
      rw [show ((μ : ℕ) - (m + 1)) = (ν : ℕ) by simp [hνdef], h, hνs, ih (by omega)]
      have hsplit : Finset.univ.filter (fun ν' : Fin 4 => (ν : ℕ) ≤ ν' ∧ ν' < μ) =
          insert ν (Finset.univ.filter fun ν' : Fin 4 => μ - m ≤ (ν' : ℕ) ∧ ν' < μ) := by
        ext ν'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · rintro ⟨h1, h2⟩
          rcases eq_or_lt_of_le h1 with h3 | h3
          · left; exact Fin.ext h3.symm
          · right; exact ⟨by omega, h2⟩
        · rintro (rfl | ⟨h1, h2⟩)
          · exact ⟨le_rfl, hν⟩
          · exact ⟨by omega, h2⟩
      rw [hsplit, Finset.sum_insert (by simp; omega), add_comm]
  have := hall μ le_rfl
  rw [Nat.sub_self] at this
  have hpt0 : pt 0 = x := by funext i; simp [hpt]
  rw [hpt0] at this
  rw [this]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext ν; simp

lemma card_lt_le (μ : Fin 4) : (Finset.univ.filter fun ν : Fin 4 => ν < μ).card ≤ 3 := by
  calc (Finset.univ.filter fun ν : Fin 4 => ν < μ).card ≤ (Finset.univ.erase (3 : Fin 4)).card := by
        refine Finset.card_le_card fun ν hν => ?_
        rw [Finset.mem_filter] at hν
        refine Finset.mem_erase.2 ⟨fun h => ?_, Finset.mem_univ _⟩
        rw [h] at hν
        exact absurd hν.2 (not_lt.2 (Fin.le_last μ))
    _ = 3 := by simp

lemma toNat_le {lo' hi' : ℤ} {ℓ : ℕ} (hℓ : hi' - lo' < ℓ) {t : ℤ} (ht : t ≤ hi') :
    (t - lo').toNat ≤ ℓ := by
  have : t - lo' ≤ ℓ := by omega
  omega

/-- **Cauchy–Schwarz on a bond**: `B(x, μ)² ≤ 3ℓΣ_{ν < μ}Σ_k(∂B)(r_ν(x⁻_ν + k, x), ν, μ)²`. -/
lemma bond_sq_le (ℓ : ℕ) (hℓ : ∀ μ, hi μ - lo μ < ℓ) (B : (Fin 4 → ℤ) → Fin 4 → ℝ)
    (htree : ∀ μ x, x ∈ box lo hi → x + e μ ∈ box lo hi → (∀ i < μ, x i = lo i) → B x μ = 0)
    {μ : Fin 4} {x : Fin 4 → ℤ} (hx : x ∈ bonds lo hi μ) :
    B x μ ^ 2 ≤ 3 * ℓ * ∑ ν ∈ Finset.univ.filter (· < μ), ∑ k ∈ Finset.range (x ν - lo ν).toNat,
      dB B (r lo ν (lo ν + k) x) ν μ ^ 2 := by
  have hx' := Finset.mem_filter.1 hx
  rw [strip B htree hx'.1 hx'.2]
  have hxb := mem_box.1 hx'.1
  calc (∑ ν ∈ Finset.univ.filter (· < μ), ∑ k ∈ Finset.range (x ν - lo ν).toNat,
        dB B (r lo ν (lo ν + k) x) ν μ) ^ 2
      ≤ (Finset.univ.filter fun ν : Fin 4 => ν < μ).card * ∑ ν ∈ Finset.univ.filter (· < μ),
          (∑ k ∈ Finset.range (x ν - lo ν).toNat, dB B (r lo ν (lo ν + k) x) ν μ) ^ 2 :=
        sq_sum_le_card_mul_sum_sq
    _ ≤ 3 * ∑ ν ∈ Finset.univ.filter (· < μ), (ℓ * ∑ k ∈ Finset.range (x ν - lo ν).toNat,
          dB B (r lo ν (lo ν + k) x) ν μ ^ 2) := by
        refine mul_le_mul (by exact_mod_cast card_lt_le μ) (Finset.sum_le_sum fun ν _ => ?_)
          (Finset.sum_nonneg fun ν _ => sq_nonneg _) (by norm_num)
        refine sq_sum_le_card_mul_sum_sq.trans (mul_le_mul_of_nonneg_right ?_
          (Finset.sum_nonneg fun k _ => sq_nonneg _))
        rw [Finset.card_range]
        exact_mod_cast toNat_le (hℓ ν) (hxb ν).2
    _ = 3 * ℓ * ∑ ν ∈ Finset.univ.filter (· < μ), ∑ k ∈ Finset.range (x ν - lo ν).toNat,
          dB B (r lo ν (lo ν + k) x) ν μ ^ 2 := by
        rw [← Finset.mul_sum, mul_assoc]

/-- **A plaquette lies in at most `ℓ³` strips**. -/
lemma strip_count (ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓ : ∀ μ, hi μ - lo μ < ℓ) {ν μ : Fin 4} (hνμ : ν < μ)
    (g : (Fin 4 → ℤ) → ℝ) (hg : ∀ y, 0 ≤ g y) :
    ∑ x ∈ bonds lo hi μ, ∑ k ∈ Finset.range (x ν - lo ν).toNat, g (r lo ν (lo ν + k) x) ≤
      (ℓ : ℝ) ^ 3 * ∑ y ∈ plaq lo hi ν μ, g y := by
  set S := (bonds lo hi μ).sigma fun x => Finset.range (x ν - lo ν).toNat with hS
  set φ : (Σ _ : Fin 4 → ℤ, ℕ) → Fin 4 → ℤ := fun z => r lo ν (lo ν + z.2) z.1 with hφ
  rw [Finset.sum_sigma' (bonds lo hi μ) (fun x => Finset.range (x ν - lo ν).toNat)
    (fun x k => g (r lo ν (lo ν + k) x))]
  have hmaps : ∀ z ∈ S, φ z ∈ plaq lo hi ν μ := by
    intro z hz
    obtain ⟨hx, hk⟩ := Finset.mem_sigma.1 hz
    have hx' := Finset.mem_filter.1 hx
    have hxb := mem_box.1 hx'.1
    have hk' : (z.2 : ℤ) + 1 ≤ z.1 ν - lo ν := by
      have := Finset.mem_range.1 hk
      have h2 := Int.toNat_of_nonneg (sub_nonneg.2 (hxb ν).1)
      omega
    have hxe_ν : (z.1 + e μ) ν = z.1 ν := by rw [add_e_apply]; simp [hνμ.ne]
    refine Finset.mem_filter.2 ⟨r_mem hx'.1 (by omega) (by omega), ?_, ?_⟩
    · simp only [hφ]; rw [r_add_e_self]; exact r_mem hx'.1 (by omega) (by omega)
    · simp only [hφ]; rw [r_add_e_gt hνμ]; exact r_mem hx'.2 (by omega) (by rw [hxe_ν]; omega)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  refine Finset.sum_le_sum fun y hy => ?_
  have hfib : ∀ z ∈ S.filter (fun z => φ z = y), g (φ z) = g y := fun z hz => by
    rw [(Finset.mem_filter.1 hz).2]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (hg y)
  -- the fibre injects into the points of `Λ` with the coordinates `> ν` of `y`
  set T := Fintype.piFinset fun i : Fin 4 => if ν < i then ({y i} : Finset ℤ) else Finset.Icc (lo i) (hi i) with hT
  have hinj : Set.InjOn (fun z : (Σ _ : Fin 4 → ℤ, ℕ) => z.1) (S.filter fun z => φ z = y) := by
    intro z hz z' hz' h
    have h1 := (Finset.mem_filter.1 hz).2
    have h2 := (Finset.mem_filter.1 hz').2
    have hk : (z.2 : ℤ) = z'.2 := by
      have e1 := congrFun h1 ν
      have e2 := congrFun h2 ν
      simp only [hφ, r, lt_irrefl, if_false, if_true] at e1 e2
      omega
    exact Sigma.ext h (heq_of_eq (by exact_mod_cast hk))
  have hsub : (S.filter fun z => φ z = y).image (fun z => z.1) ⊆ T := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hx
    have hzS := (Finset.mem_filter.1 hz).1
    have hzy := (Finset.mem_filter.1 hz).2
    have hxb := mem_box.1 (Finset.mem_filter.1 (Finset.mem_sigma.1 hzS).1).1
    rw [hT, Fintype.mem_piFinset]
    intro i
    by_cases hi : ν < i
    · rw [if_pos hi, Finset.mem_singleton]
      have := congrFun hzy i
      simp only [hφ, r, not_lt.2 hi.le, if_false, hi.ne', if_false] at this
      exact this
    · rw [if_neg hi, Finset.mem_Icc]; exact hxb i
  have hcard : ((S.filter fun z => φ z = y).card : ℝ) ≤ (T.card : ℝ) := by
    rw [← Finset.card_image_of_injOn hinj]
    exact_mod_cast Finset.card_le_card hsub
  refine hcard.trans ?_
  rw [hT, Fintype.card_piFinset, Fin.prod_univ_four]
  have hν3 : ν < 3 := lt_of_lt_of_le hνμ (Fin.le_last μ)
  have hc : ∀ i : Fin 4, ((if ν < i then ({y i} : Finset ℤ) else Finset.Icc (lo i) (hi i)).card : ℝ) ≤ ℓ := by
    intro i
    split_ifs
    · simp; exact_mod_cast hℓ1
    · rw [Int.card_Icc]
      have := hℓ i
      have h0 : ((hi i + 1 - lo i).toNat : ℝ) ≤ ℓ := by exact_mod_cast (by omega : (hi i + 1 - lo i).toNat ≤ ℓ)
      exact h0
  have h3 : ((if ν < 3 then ({y 3} : Finset ℤ) else Finset.Icc (lo 3) (hi 3)).card : ℝ) = 1 := by
    rw [if_pos hν3]; simp
  push_cast
  rw [h3, mul_one]
  have hℓ0 : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg _
  calc _ ≤ (ℓ : ℝ) * ℓ * ℓ := by
        refine mul_le_mul (mul_le_mul (hc 0) (hc 1) (Nat.cast_nonneg _) hℓ0) (hc 2) (Nat.cast_nonneg _)
          (mul_nonneg hℓ0 hℓ0)
    _ = (ℓ : ℝ) ^ 3 := by ring

/-- **`eq:axial-poincare`**: `Σ_bB(b)² ≤ 4ℓ⁵Σ_p(∂B)(p)²` for `B` vanishing on the tree of the axial gauge. -/
theorem axial_poincare (ℓ : ℕ) (hℓ : ∀ μ, hi μ - lo μ < ℓ) (B : (Fin 4 → ℤ) → Fin 4 → ℝ)
    (htree : ∀ μ x, x ∈ box lo hi → x + e μ ∈ box lo hi → (∀ i < μ, x i = lo i) → B x μ = 0) :
    ∑ μ, ∑ x ∈ bonds lo hi μ, B x μ ^ 2 ≤
      4 * (ℓ : ℝ) ^ 5 * ∑ μ, ∑ ν ∈ Finset.univ.filter (· < μ), ∑ y ∈ plaq lo hi ν μ, dB B y ν μ ^ 2 := by
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ1
  · -- the box is empty
    have hempty : box lo hi = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      have := (mem_box.1 hx) 0
      have := hℓ 0
      push_cast at this
      omega
    simp [bonds, hempty]
  have hP : 0 ≤ ∑ μ, ∑ ν ∈ Finset.univ.filter (· < μ), ∑ y ∈ plaq lo hi ν μ, dB B y ν μ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc ∑ μ, ∑ x ∈ bonds lo hi μ, B x μ ^ 2
      ≤ ∑ μ, ∑ x ∈ bonds lo hi μ, 3 * ℓ * ∑ ν ∈ Finset.univ.filter (· < μ),
          ∑ k ∈ Finset.range (x ν - lo ν).toNat, dB B (r lo ν (lo ν + k) x) ν μ ^ 2 :=
        Finset.sum_le_sum fun μ _ => Finset.sum_le_sum fun x hx => bond_sq_le ℓ hℓ B htree hx
    _ = 3 * ℓ * ∑ μ, ∑ ν ∈ Finset.univ.filter (· < μ), ∑ x ∈ bonds lo hi μ,
          ∑ k ∈ Finset.range (x ν - lo ν).toNat, dB B (r lo ν (lo ν + k) x) ν μ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ 3 * ℓ * ∑ μ, ∑ ν ∈ Finset.univ.filter (· < μ), (ℓ : ℝ) ^ 3 * ∑ y ∈ plaq lo hi ν μ, dB B y ν μ ^ 2 := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun μ _ => Finset.sum_le_sum fun ν hν => ?_)
          (by positivity)
        exact strip_count ℓ hℓ1 hℓ (Finset.mem_filter.1 hν).2 (fun y => dB B y ν μ ^ 2) fun y => sq_nonneg _
    _ = 3 * (ℓ : ℝ) ^ 4 * ∑ μ, ∑ ν ∈ Finset.univ.filter (· < μ), ∑ y ∈ plaq lo hi ν μ, dB B y ν μ ^ 2 := by
        simp only [← Finset.mul_sum]; ring
    _ ≤ 4 * (ℓ : ℝ) ^ 5 * ∑ μ, ∑ ν ∈ Finset.univ.filter (· < μ), ∑ y ∈ plaq lo hi ν μ, dB B y ν μ ^ 2 := by
        refine mul_le_mul_of_nonneg_right ?_ hP
        have h1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ1
        nlinarith [pow_le_pow_left₀ zero_le_one h1 4, pow_nonneg (Nat.cast_nonneg (α := ℝ) ℓ) 4]

end Axial
end CoreLean

end
