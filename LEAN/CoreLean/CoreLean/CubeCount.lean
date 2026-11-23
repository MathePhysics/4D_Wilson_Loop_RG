/-
`lem:cube-count` of BALABAN_CORE.tex, the sum over domains `eq:domain-sum`.

The cubes of a grid are the vertices of the graph `wallGraph R` on `Fin 4 → R` (`R = ℤ` for the
lattice, `R = ZMod n` for the torus) in which two cubes are adjacent if they share a wall, that is,
if their centres differ by `±s` in one coordinate; a union of cubes is connected in the sense of
`def:localisation`(i) if the induced subgraph is connected. Every cube has at most eight neighbours.

`domain_sum` is the bound `eq:domain-sum` for any size function `d ≥ 0` which satisfies the first
bound of `eq:cube-count`, `#(X) ≤ 2⁸(2 + d(X))`; the proof is the core's: the connected unions of `n`
cubes containing a given cube number at most `8^{2(n-1)}` (`Balaban.Polymer.card_animals_le`), and for
`n ≥ 2¹⁰` the first bound gives `d(X) ≥ 2⁻⁹n`.
-/
import CoreLean.Vendor.Animals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ZMod.Defs

open SimpleGraph Real Balaban.Polymer

namespace CoreLean

/-! ### The graph of the cubes of a grid -/

section WallGraph

variable (R : Type*) [Ring R] [DecidableEq R]

/-- The neighbours of a cube: the centre moved by `±1` in one coordinate. -/
def wallNbr (a : Fin 4 → R) (p : Fin 4 × Bool) : Fin 4 → R :=
  if p.2 then a + Pi.single p.1 1 else a - Pi.single p.1 1

/-- Two cubes share a wall: their centres differ by `±1` in one coordinate. -/
def wallGraph : SimpleGraph (Fin 4 → R) where
  Adj a b := a ≠ b ∧ ∃ p, b = wallNbr R a p
  symm := ⟨fun a b => by
    rintro ⟨hab, ⟨μ, s⟩, rfl⟩
    refine ⟨hab.symm, ⟨μ, !s⟩, ?_⟩
    cases s <;> simp [wallNbr]⟩
  loopless := ⟨fun a h => h.1 rfl⟩

instance (a : Fin 4 → R) : Fintype ((wallGraph R).neighborSet a) :=
  Fintype.ofFinset ((Finset.univ.image (wallNbr R a)).filter (· ≠ a)) fun b => by
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
      mem_neighborSet, wallGraph]
    constructor
    · rintro ⟨⟨p, rfl⟩, h⟩; exact ⟨Ne.symm h, p, rfl⟩
    · rintro ⟨h, p, rfl⟩; exact ⟨⟨p, rfl⟩, Ne.symm h⟩

instance : (wallGraph R).LocallyFinite := fun a => inferInstance

/-- Every cube shares a wall with at most eight cubes. -/
theorem wallGraph_degree_le (a : Fin 4 → R) : (wallGraph R).degree a ≤ 8 := by
  classical
  rw [← card_neighborFinset_eq_degree]
  have : (wallGraph R).neighborFinset a ⊆ Finset.univ.image (wallNbr R a) := by
    intro b hb
    rw [mem_neighborFinset] at hb
    obtain ⟨-, p, rfl⟩ := hb
    exact Finset.mem_image_of_mem _ (Finset.mem_univ p)
  refine (Finset.card_le_card this).trans (Finset.card_image_le.trans ?_)
  simp

end WallGraph

/-! ### Two numerical facts -/

/-- `Σ_{n < N} 64^{n-1} ≤ 2 · 64^{N-1}` for `N ≥ 1`. -/
lemma sum_range_pow_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.range N, (64 : ℝ) ^ (n - 1) ≤ 2 * 64 ^ (N - 1) := by
  induction N with
  | zero => omega
  | succ N ih =>
    rcases Nat.eq_zero_or_pos N with rfl | hN'
    · simp
    · rw [Finset.sum_range_succ]
      have := ih hN'
      have h64 : (64 : ℝ) ^ N = 64 * 64 ^ (N - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel hN']
      rw [Nat.add_sub_cancel, h64]
      have : (0 : ℝ) ≤ 64 ^ (N - 1) := by positivity
      linarith

/-- `Σ_{n ∈ S} e^{-n} ≤ 1` for a finite set `S` of positive integers. -/
lemma sum_exp_neg_le_one (S : Finset ℕ) (hS : ∀ n ∈ S, 1 ≤ n) :
    ∑ n ∈ S, Real.exp (-(n : ℝ)) ≤ 1 := by
  have hq : Real.exp (-1) < 1 := by
    have := Real.exp_lt_exp.mpr (show (-1 : ℝ) < 0 by norm_num); simpa using this
  have hq0 : 0 ≤ Real.exp (-1) := (Real.exp_pos _).le
  have hgeom : HasSum (fun n : ℕ => Real.exp (-1) ^ n) (1 - Real.exp (-1))⁻¹ :=
    hasSum_geometric_of_lt_one hq0 hq
  have hexp : ∀ n : ℕ, Real.exp (-(n : ℝ)) = Real.exp (-1) ^ n := fun n => by
    rw [← Real.exp_nat_mul]; ring_nf
  -- `Σ_{n ∈ S} e^{-n} ≤ Σ_{n ≥ 1} e^{-n} = e^{-1}/(1 - e^{-1}) ≤ 1`
  have hsub : ∑ n ∈ S, Real.exp (-(n : ℝ)) ≤ ∑' n : ℕ, Real.exp (-1) ^ n - 1 := by
    have hS' : (0 : ℕ) ∉ S := fun h => by have := hS 0 h; omega
    have h1 := hgeom.summable.sum_le_tsum (insert 0 S) fun n _ => pow_nonneg hq0 n
    rw [Finset.sum_insert hS', pow_zero] at h1
    simp_rw [hexp]
    linarith
  rw [hgeom.tsum_eq] at hsub
  refine hsub.trans ?_
  -- `(1 - q)⁻¹ - 1 ≤ 1` iff `q ≤ 1/2`, and `e^{-1} ≤ 1/2` since `e ≥ 2`
  have he : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    have := Real.add_one_le_exp (1 : ℝ)
    norm_num at this ⊢; linarith
  have hpos : 0 < 1 - Real.exp (-1) := by linarith
  rw [sub_le_iff_le_add, inv_le_comm₀ hpos (by norm_num)]
  linarith

/-! ### The sum over domains -/

section DomainSum

variable {V : Type*} (G : SimpleGraph V) [G.LocallyFinite]

/-- The term bound: the connected sets of `n` vertices containing `x`, weighted by `e^{-κ d}`, sum to
at most `8^{2(n-1)}` for every `n`, and to at most `e^{-n}` for `n ≥ 2¹⁰`. -/
lemma sum_animals_le (hΔ : ∀ v, G.degree v ≤ 8) {d : Finset V → ℝ} (hd0 : ∀ X, 0 ≤ d X)
    {x : V} (hcount : ∀ X : Finset V, x ∈ X → (G.induce (X : Set V)).Connected →
      (X.card : ℝ) ≤ 2 ^ 8 * (2 + d X))
    {κ : ℝ} (hκ : 2 ^ 9 * (6 * Real.log 2 + 1) ≤ κ) (n : ℕ) (T : Finset (Finset V))
    (hT : T ⊆ animals G x n) :
    ∑ X ∈ T, Real.exp (-κ * d X) ≤ (64 : ℝ) ^ (n - 1) ∧
      (2 ^ 10 ≤ n → ∑ X ∈ T, Real.exp (-κ * d X) ≤ Real.exp (-(n : ℝ))) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hκ0 : 0 ≤ κ := le_trans (by positivity) hκ
  have hcard : (T.card : ℝ) ≤ (64 : ℝ) ^ (n - 1) := by
    have := (Finset.card_le_card hT).trans (card_animals_le G hΔ x n)
    calc (T.card : ℝ) ≤ ((8 ^ (2 * (n - 1)) : ℕ) : ℝ) := by exact_mod_cast this
      _ = (64 : ℝ) ^ (n - 1) := by push_cast; rw [pow_mul]; norm_num
  constructor
  · calc ∑ X ∈ T, Real.exp (-κ * d X) ≤ ∑ _X ∈ T, (1 : ℝ) :=
          Finset.sum_le_sum fun X _ => by
            rw [Real.exp_le_one_iff]; nlinarith [hd0 X]
      _ = T.card := by simp
      _ ≤ _ := hcard
  · intro hn
    have hn1 : (2 : ℝ) ^ 10 ≤ n := by exact_mod_cast hn
    -- every term is at most `2^{-6n} e^{-n}`
    have hterm : ∀ X ∈ T, Real.exp (-κ * d X) ≤ (2 : ℝ) ^ (-(6 * n : ℝ)) * Real.exp (-(n : ℝ)) := by
      intro X hX
      obtain ⟨hx, hc, hconn⟩ := (mem_animals G).1 (hT hX)
      have h1 := hcount X hx hconn
      rw [hc] at h1
      -- `d(X) ≥ 2⁻⁸ n - 2 ≥ 2⁻⁹ n`
      have hd : (n : ℝ) / 2 ^ 9 ≤ d X := by
        have : (n : ℝ) / 2 ^ 8 - 2 ≤ d X := by
          rw [div_sub' (by norm_num), div_le_iff₀ (by norm_num)]; linarith
        refine le_trans ?_ this
        rw [div_le_iff₀ (by norm_num), sub_mul, div_mul_eq_mul_div, mul_div_assoc]
        norm_num; linarith
      have hκd : (6 * Real.log 2 + 1) * n ≤ κ * d X := by
        calc (6 * Real.log 2 + 1) * n = 2 ^ 9 * (6 * Real.log 2 + 1) * ((n : ℝ) / 2 ^ 9) := by
              field_simp
          _ ≤ κ * d X := mul_le_mul hκ hd (by positivity) hκ0
      rw [Real.rpow_def_of_pos (by norm_num), ← Real.exp_add, Real.exp_le_exp]
      nlinarith
    calc ∑ X ∈ T, Real.exp (-κ * d X)
        ≤ ∑ _X ∈ T, (2 : ℝ) ^ (-(6 * n : ℝ)) * Real.exp (-(n : ℝ)) := Finset.sum_le_sum hterm
      _ = T.card * ((2 : ℝ) ^ (-(6 * n : ℝ)) * Real.exp (-(n : ℝ))) := by simp
      _ ≤ (64 : ℝ) ^ n * ((2 : ℝ) ^ (-(6 * n : ℝ)) * Real.exp (-(n : ℝ))) := by
          refine mul_le_mul_of_nonneg_right (hcard.trans ?_) (by positivity)
          exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le n 1)
      _ = Real.exp (-(n : ℝ)) := by
          rw [← mul_assoc, show (64 : ℝ) = 2 ^ (6 : ℝ) by norm_num, ← Real.rpow_natCast,
            ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
          simp

/-- `eq:domain-sum`: for `κ ≥ 2⁹(6 log 2 + 1)` and every vertex `x`, every finite family of connected
sets containing `x` satisfies `Σ_X e^{-κ d(X)} ≤ 2^{6·2¹⁰} + 1`. -/
theorem domain_sum_finset (hΔ : ∀ v, G.degree v ≤ 8) {d : Finset V → ℝ} (hd0 : ∀ X, 0 ≤ d X)
    {x : V} (hcount : ∀ X : Finset V, x ∈ X → (G.induce (X : Set V)).Connected →
      (X.card : ℝ) ≤ 2 ^ 8 * (2 + d X))
    {κ : ℝ} (hκ : 2 ^ 9 * (6 * Real.log 2 + 1) ≤ κ) (F : Finset (Finset V))
    (hF : ∀ X ∈ F, x ∈ X ∧ (G.induce (X : Set V)).Connected) :
    ∑ X ∈ F, Real.exp (-κ * d X) ≤ 2 ^ (6 * 2 ^ 10) + 1 := by
  classical
  -- sort by the number of vertices
  set S := F.image Finset.card with hS
  rw [← Finset.sum_fiberwise_of_maps_to (g := Finset.card) (t := S)
    fun X hX => Finset.mem_image_of_mem _ hX]
  have hfib : ∀ n, F.filter (fun X => X.card = n) ⊆ animals G x n := fun n X hX => by
    rw [Finset.mem_filter] at hX
    exact (mem_animals G).2 ⟨(hF X hX.1).1, hX.2, (hF X hX.1).2⟩
  have hS1 : ∀ n ∈ S, 1 ≤ n := fun n hn => by
    obtain ⟨X, hX, rfl⟩ := Finset.mem_image.1 hn
    exact Finset.card_pos.2 ⟨x, (hF X hX).1⟩
  rw [← Finset.sum_filter_add_sum_filter_not S (fun n => n < 2 ^ 10)]
  refine add_le_add ?_ ?_
  · calc ∑ n ∈ S.filter (· < 2 ^ 10), ∑ X ∈ F with X.card = n, Real.exp (-κ * d X)
        ≤ ∑ n ∈ Finset.range (2 ^ 10), (64 : ℝ) ^ (n - 1) := by
          refine (Finset.sum_le_sum fun n _ =>
            (sum_animals_le G hΔ hd0 hcount hκ n _ (hfib n)).1).trans ?_
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) fun n _ _ => by positivity
          rw [Finset.mem_filter] at hn
          exact Finset.mem_range.2 hn.2
      _ ≤ 2 * 64 ^ (2 ^ 10 - 1) := sum_range_pow_le _ (by norm_num)
      _ ≤ 2 ^ (6 * 2 ^ 10) := by
          rw [show (64 : ℝ) = 2 ^ 6 by norm_num, ← pow_mul, ← pow_succ']
          exact pow_le_pow_right₀ (by norm_num) (by norm_num)
  · calc ∑ n ∈ S.filter (fun n => ¬n < 2 ^ 10), ∑ X ∈ F with X.card = n, Real.exp (-κ * d X)
        ≤ ∑ n ∈ S.filter (fun n => ¬n < 2 ^ 10), Real.exp (-(n : ℝ)) :=
          Finset.sum_le_sum fun n hn => by
            rw [Finset.mem_filter, not_lt] at hn
            exact (sum_animals_le G hΔ hd0 hcount hκ n _ (hfib n)).2 hn.2
      _ ≤ 1 := sum_exp_neg_le_one _ fun n hn => hS1 n (Finset.mem_filter.1 hn).1

/-- `eq:domain-sum` as a sum over all connected finite sets containing `x`. -/
theorem domain_sum (hΔ : ∀ v, G.degree v ≤ 8) {d : Finset V → ℝ} (hd0 : ∀ X, 0 ≤ d X)
    {x : V} (hcount : ∀ X : Finset V, x ∈ X → (G.induce (X : Set V)).Connected →
      (X.card : ℝ) ≤ 2 ^ 8 * (2 + d X))
    {κ : ℝ} (hκ : 2 ^ 9 * (6 * Real.log 2 + 1) ≤ κ) :
    Summable (fun X : {X : Finset V // x ∈ X ∧ (G.induce (X : Set V)).Connected} =>
      Real.exp (-κ * d X.1)) ∧
    ∑' X : {X : Finset V // x ∈ X ∧ (G.induce (X : Set V)).Connected},
      Real.exp (-κ * d X.1) ≤ 2 ^ (6 * 2 ^ 10) + 1 := by
  classical
  have hfin : ∀ u : Finset {X : Finset V // x ∈ X ∧ (G.induce (X : Set V)).Connected},
      ∑ X ∈ u, Real.exp (-κ * d X.1) ≤ 2 ^ (6 * 2 ^ 10) + 1 := fun u => by
    have h := Finset.sum_map u (Function.Embedding.subtype _) (fun X => Real.exp (-κ * d X))
    simp only [Function.Embedding.coe_subtype] at h
    rw [← h]
    refine domain_sum_finset G hΔ hd0 hcount hκ _ fun X hX => ?_
    obtain ⟨Y, -, rfl⟩ := Finset.mem_map.1 hX
    exact Y.2
  have hs := summable_of_sum_le (fun X => (Real.exp_pos _).le) hfin
  exact ⟨hs, hs.tsum_le_of_sum_le hfin⟩

end DomainSum

end CoreLean
