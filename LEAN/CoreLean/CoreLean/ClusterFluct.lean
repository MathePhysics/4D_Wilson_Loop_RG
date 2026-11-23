/-
`lem:fluctuation-kp` of BALABAN_CORE.tex (`9c56d4590aff`) on the grid of `ClusterGrid.lean`: for activities with
`|H(Z)| ≤ e^{-5κ}e^{-κd(Z)}`, `κ ≥ κ_vac = 2⁹(1 + 16 log 2)`, and `c = (9/64)e^{-4κ}`:
(i) `Σ_{Z ≁ M}|H(Z)|e^{c#(Z)}2^{9#(Z)} ≤ c#(M)`; (ii) `Σ_{𝒞 ≁ M}|φ^T(𝒞)|2^{9#(𝒞)} ≤ c#(M)`; (iii) the polymer sum over
the polymers compatible with `M` (or over all) is `exp Σ_𝒞φ^T(𝒞)`, absolutely convergent; (iv) the same with the weight
`2^{9#}e^{#}` and the suprema over a parameter set, for `κ ≥ 2⁹(2 + 16 log 2)`.
The proof is the core's: `#(Z) ≤ 2⁹(1 + d(Z))` gives `|H| ≤ e^{-4κ}e^{-λ#}`, `λ = 2⁻⁹κ`; at most `64^{n-1}` polymers of
`n` cubes contain a given cube; `9#(M)` cubes meet `M` or share a wall with it; the geometric series. (ii) is
`lem:cluster-bounds` with `h̄ = |H|`, `a = c#`, `d = 9 log 2 #`. (iii) uses the abstract theorem of `ClusterLogXi.lean`
with the criterion (i) in place of the core's appeal to `thm:polymer-logarithm` at `ε = e^{-5κ}`.
-/
import CoreLean.ClusterGrid

open Finset

noncomputable section

namespace CoreLean
namespace PolymerGrid

open Classical
open TreeGraph

variable {s : ℝ} {N : ℕ} [NeZero N]

/-- `κ_vac = 2⁹(1 + 16 log 2)`. -/
def kappaVac : ℝ := 2 ^ 9 * (1 + 16 * Real.log 2)

/-- `c = (9/64)e^{-4κ}`. -/
def cKP (κ : ℝ) : ℝ := 9 / 64 * Real.exp (-4 * κ)

lemma log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

/-- Each polymer `≁ M` contains a cube of `nbhd M`. -/
lemma sum_notSim_le (P : Finset (Finset (Cube N))) (M : Finset (Cube N)) (g : P → ℝ) (hg0 : ∀ Z, 0 ≤ g Z) :
    ∑ Z ∈ (Finset.univ : Finset P).filter (fun Z => NotSim Z.1 M), g Z ≤
      ∑ y ∈ nbhd M, ∑ Z ∈ (Finset.univ : Finset P).filter (fun Z => y ∈ Z.1), g Z := by
  calc ∑ Z ∈ (Finset.univ : Finset P).filter (fun Z => NotSim Z.1 M), g Z
      ≤ ∑ Z ∈ (Finset.univ : Finset P).filter (fun Z => NotSim Z.1 M),
          ∑ y ∈ nbhd M, (if y ∈ Z.1 then g Z else 0) := by
        refine Finset.sum_le_sum fun Z hZ => ?_
        obtain ⟨c, hcZ, hcM⟩ := exists_mem_nbhd (Finset.mem_filter.1 hZ).2
        calc g Z = (if c ∈ Z.1 then g Z else 0) := (if_pos hcZ).symm
          _ ≤ _ := Finset.single_le_sum (f := fun y => if y ∈ Z.1 then g Z else 0)
              (fun y _ => by split_ifs; exact hg0 Z; exact le_rfl) hcM
    _ ≤ ∑ Z : P, ∑ y ∈ nbhd M, (if y ∈ Z.1 then g Z else 0) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun Z _ _ =>
          Finset.sum_nonneg fun y _ => by split_ifs; exact hg0 Z; exact le_rfl
    _ = ∑ y ∈ nbhd M, ∑ Z ∈ (Finset.univ : Finset P).filter (fun Z => y ∈ Z.1), g Z := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun y _ => (Finset.sum_filter _ _).symm

/-- The polymers of `n` cubes containing a cube `y` are at most `64^{n-1}`, so for `e^{-x} ≤ 2⁻⁷` the polymers
containing `y` satisfy `Σ_Ze^{-x#(Z)} ≤ 1/64`. -/
lemma sum_animal_weights (P : Finset (Finset (Cube N))) (hP : ∀ Z ∈ P, IsConn Z) (y : Cube N) {x : ℝ}
    (hx : 7 * Real.log 2 ≤ x) :
    ∑ Z ∈ (Finset.univ : Finset P).filter (fun Z => y ∈ Z.1), Real.exp (-x * Z.1.card) ≤ 1 / 64 := by
  set T := (Finset.univ : Finset P).filter (fun Z => y ∈ Z.1) with hT
  have hex : Real.exp (-x) ≤ 1 / 128 := by
    calc Real.exp (-x) ≤ Real.exp (-(7 * Real.log 2)) := Real.exp_le_exp.2 (by linarith)
      _ = 1 / 128 := by
          rw [Real.exp_neg, show 7 * Real.log 2 = (7 : ℕ) * Real.log 2 by norm_num, Real.exp_nat_mul,
            Real.exp_log (by norm_num)]
          norm_num
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun Z : P => Z.1.card) (t := T.image fun Z => Z.1.card)
    fun Z hZ => Finset.mem_image_of_mem _ hZ]
  have hS1 : ∀ n ∈ T.image (fun Z : P => Z.1.card), 1 ≤ n := fun n hn => by
    obtain ⟨Z, hZ, rfl⟩ := Finset.mem_image.1 hn
    exact Finset.card_pos.2 ⟨y, (Finset.mem_filter.1 hZ).2⟩
  have hlayer : ∀ n ∈ T.image (fun Z : P => Z.1.card),
      ∑ Z ∈ T with Z.1.card = n, Real.exp (-x * Z.1.card) ≤ 1 / 64 * (1 / 2) ^ n := by
    intro n hn
    have hn1 := hS1 n hn
    have hcount : ((T.filter fun Z : P => Z.1.card = n).card : ℝ) ≤ (64 : ℝ) ^ (n - 1) := by
      have h1 : (T.filter fun Z : P => Z.1.card = n).card ≤
          (Balaban.Polymer.animals (wallGraph (ZMod N)) y n).card := by
        refine Finset.card_le_card_of_injOn (fun Z => Z.1) (fun Z hZ => ?_) (fun Z _ Z' _ h => Subtype.ext h)
        rw [Finset.mem_filter] at hZ
        exact (Balaban.Polymer.mem_animals _).2 ⟨(Finset.mem_filter.1 hZ.1).2, hZ.2, hP Z.1 Z.2⟩
      have h2 := Balaban.Polymer.card_animals_le (wallGraph (ZMod N)) (wallGraph_degree_le _) y n
      calc ((T.filter fun Z : P => Z.1.card = n).card : ℝ) ≤ ((8 ^ (2 * (n - 1)) : ℕ) : ℝ) := by
            exact_mod_cast h1.trans h2
        _ = (64 : ℝ) ^ (n - 1) := by push_cast; rw [pow_mul]; norm_num
    calc ∑ Z ∈ T with Z.1.card = n, Real.exp (-x * Z.1.card)
        = ∑ Z ∈ T with Z.1.card = n, Real.exp (-x) ^ n := Finset.sum_congr rfl fun Z hZ => by
          rw [(Finset.mem_filter.1 hZ).2, ← Real.exp_nat_mul]; ring_nf
      _ = (T.filter fun Z : P => Z.1.card = n).card * Real.exp (-x) ^ n := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (64 : ℝ) ^ (n - 1) * (1 / 128) ^ n :=
          mul_le_mul hcount (pow_le_pow_left₀ (Real.exp_pos _).le hex n) (by positivity) (by positivity)
      _ = 1 / 64 * (1 / 2) ^ n := by
          obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
          rw [Nat.add_sub_cancel, pow_succ, pow_succ, pow_succ]
          rw [show (1 / 128 : ℝ) = 1 / 64 * (1 / 2) by norm_num, mul_pow]
          ring
  refine (Finset.sum_le_sum hlayer).trans ?_
  rw [← Finset.mul_sum]
  have hgeo : ∑ n ∈ T.image (fun Z : P => Z.1.card), (1 / 2 : ℝ) ^ n ≤ 1 := by
    have h0 : (0 : ℕ) ∉ T.image (fun Z : P => Z.1.card) := fun h => by have := hS1 0 h; omega
    have h := sum_le_tsum (insert 0 (T.image fun Z : P => Z.1.card)) (fun n _ => by positivity)
      (summable_geometric_two)
    rw [Finset.sum_insert h0, tsum_geometric_two] at h
    simp only [pow_zero] at h
    have e : ∀ n : ℕ, (1 / 2 : ℝ) ^ n = ((1 : ℝ) / 2) ^ n := fun n => rfl
    linarith
  calc 1 / 64 * ∑ n ∈ T.image (fun Z : P => Z.1.card), (1 / 2 : ℝ) ^ n ≤ 1 / 64 * 1 :=
        mul_le_mul_of_nonneg_left hgeo (by norm_num)
    _ = 1 / 64 := mul_one _

variable (hs : 0 < s)
include hs

/-- **The criterion with a weight `e^{δ#}`**: for `δ ≥ 0`, `κ ≥ 2⁹(1 + δ + 16 log 2)`, `c = (9/64)e^{-4κ}` and
`0 ≤ H̄(Z) ≤ e^{-5κ}e^{-κd(Z)}`, every union `M` of cubes satisfies
`Σ_{Z ≁ M}H̄(Z)e^{c#(Z) + (9 log 2 + δ)#(Z)} ≤ c#(M)`. -/
theorem kp_weighted (P : Finset (Finset (Cube N))) (hP : ∀ Z ∈ P, IsConn Z) {κ δ : ℝ} (hδ : 0 ≤ δ)
    (hκ : 2 ^ 9 * (1 + δ + 16 * Real.log 2) ≤ κ) (Hb : P → ℝ) (hHb0 : ∀ Z, 0 ≤ Hb Z)
    (hHb : ∀ Z, Hb Z ≤ Real.exp (-5 * κ) * Real.exp (-κ * size s N Z.1)) (M : Finset (Cube N)) :
    ∑ Z ∈ (Finset.univ : Finset P).filter (fun Z => NotSim Z.1 M),
      Hb Z * Real.exp (cKP κ * Z.1.card + (9 * Real.log 2 + δ) * Z.1.card) ≤ cKP κ * M.card := by
  have hl2 := log_two_pos
  have hκ0 : 0 ≤ κ := le_trans (by positivity) hκ
  have hc1 : cKP κ ≤ 1 := by
    unfold cKP
    have : Real.exp (-4 * κ) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    nlinarith [Real.exp_pos (-4 * κ)]
  have hc0 : 0 ≤ cKP κ := by unfold cKP; positivity
  set x := κ / 2 ^ 9 - cKP κ - 9 * Real.log 2 - δ with hxdef
  have hx : 7 * Real.log 2 ≤ x := by
    have : 1 + δ + 16 * Real.log 2 ≤ κ / 2 ^ 9 := by rw [le_div_iff₀ (by norm_num)]; linarith
    rw [hxdef]; linarith
  -- each term is at most `e^{-4κ}e^{-x#(Z)}`
  have hterm : ∀ Z : P, Hb Z * Real.exp (cKP κ * Z.1.card + (9 * Real.log 2 + δ) * Z.1.card) ≤
      Real.exp (-4 * κ) * Real.exp (-x * Z.1.card) := by
    intro Z
    have hcard := card_le_size hs (hP Z.1 Z.2)
    have hd := size_nonneg (N := N) hs Z.1
    -- `-κd ≤ κ - 2⁻⁹κ#`
    have hkd : -κ * size s N Z.1 ≤ κ - κ / 2 ^ 9 * Z.1.card := by
      have h1 : (Z.1.card : ℝ) / 2 ^ 9 ≤ 1 + size s N Z.1 := by
        rw [div_le_iff₀ (by norm_num)]; nlinarith
      have h2 := mul_le_mul_of_nonneg_left h1 hκ0
      have h3 : κ * ((Z.1.card : ℝ) / 2 ^ 9) = κ / 2 ^ 9 * Z.1.card := by ring
      linarith
    calc Hb Z * Real.exp (cKP κ * Z.1.card + (9 * Real.log 2 + δ) * Z.1.card)
        ≤ Real.exp (-5 * κ) * Real.exp (-κ * size s N Z.1) *
            Real.exp (cKP κ * Z.1.card + (9 * Real.log 2 + δ) * Z.1.card) :=
          mul_le_mul_of_nonneg_right (hHb Z) (Real.exp_pos _).le
      _ = Real.exp (-5 * κ + -κ * size s N Z.1 + (cKP κ * Z.1.card + (9 * Real.log 2 + δ) * Z.1.card)) := by
          rw [Real.exp_add, Real.exp_add]
      _ ≤ Real.exp (-4 * κ + -x * Z.1.card) := Real.exp_le_exp.2 (by rw [hxdef]; nlinarith)
      _ = Real.exp (-4 * κ) * Real.exp (-x * Z.1.card) := Real.exp_add _ _
  calc _ ≤ ∑ Z ∈ (Finset.univ : Finset P).filter (fun Z => NotSim Z.1 M),
        Real.exp (-4 * κ) * Real.exp (-x * Z.1.card) := Finset.sum_le_sum fun Z _ => hterm Z
    _ ≤ ∑ y ∈ nbhd M, ∑ Z ∈ (Finset.univ : Finset P).filter (fun Z => y ∈ Z.1),
        Real.exp (-4 * κ) * Real.exp (-x * Z.1.card) := sum_notSim_le P M _ fun Z => by positivity
    _ ≤ ∑ y ∈ nbhd M, Real.exp (-4 * κ) * (1 / 64) := Finset.sum_le_sum fun y _ => by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (sum_animal_weights P hP y hx) (Real.exp_pos _).le
    _ = (nbhd M).card * (Real.exp (-4 * κ) * (1 / 64)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (9 * M.card : ℕ) * (Real.exp (-4 * κ) * (1 / 64)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast card_nbhd M) (by positivity)
    _ = cKP κ * M.card := by unfold cKP; push_cast; ring

lemma two_pow_eq_exp (n : ℕ) : (2 : ℝ) ^ (9 * n) = Real.exp (9 * Real.log 2 * n) := by
  rw [show (9 * Real.log 2 * n : ℝ) = ((9 * n : ℕ) : ℝ) * Real.log 2 by push_cast; ring, Real.exp_nat_mul,
    Real.exp_log (by norm_num)]

/-- **`lem:fluctuation-kp`(i)**: `Σ_{Z ≁ M}|H(Z)|e^{c#(Z)}2^{9#(Z)} ≤ c#(M)`. -/
theorem fluctuation_kp_i (P : Finset (Finset (Cube N))) (hP : ∀ Z ∈ P, IsConn Z) {κ : ℝ} (hκ : kappaVac ≤ κ)
    (H : P → ℂ) (hH : ∀ Z, ‖H Z‖ ≤ Real.exp (-5 * κ) * Real.exp (-κ * size s N Z.1)) (M : Finset (Cube N)) :
    ∑ Z ∈ (Finset.univ : Finset P).filter (fun Z => NotSim Z.1 M),
      ‖H Z‖ * Real.exp (cKP κ * Z.1.card) * 2 ^ (9 * Z.1.card) ≤ cKP κ * M.card := by
  have h := kp_weighted hs P hP le_rfl (by unfold kappaVac at hκ; linarith) (fun Z => ‖H Z‖)
    (fun Z => norm_nonneg _) hH M
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun Z _ => ?_)) h
  rw [two_pow_eq_exp, mul_assoc, ← Real.exp_add]
  ring_nf

/-- The cluster function `φ^T(Z_1, …, Z_n) = (1/n!)ρ^T(Z_1, …, Z_n)H(Z_1)⋯H(Z_n)`. -/
def phiT (P : Finset (Finset (Cube N))) (H : P → ℂ) {n : ℕ} (Z : Fin n → P) : ℂ :=
  ((n.factorial : ℂ))⁻¹ * (ursS (incP P) Z : ℂ) * ∏ i, H (Z i)

/-- `#(𝒞) = Σ_j#(Z_j)`. -/
def clCard (P : Finset (Finset (Cube N))) {n : ℕ} (Z : Fin n → P) : ℕ := ∑ i, (Z i).1.card

/-- The terms of the sum (ii) over the clusters of `k + 1` polymers which meet `M`, with the weight `e^{δ#(𝒞)}`. -/
def kpTerm (P : Finset (Finset (Cube N))) (H : P → ℂ) (M : Finset (Cube N)) (δ : ℝ) (k : ℕ) : ℝ :=
  ∑ Z : Fin (k + 1) → P, if ∃ i, NotSim (Z i).1 M then ‖phiT P H Z‖ * 2 ^ (9 * clCard P Z) * Real.exp (δ * clCard P Z)
    else 0

lemma kpTerm_eq (P : Finset (Finset (Cube N))) (H : P → ℂ) (M : Finset (Cube N)) (δ : ℝ) (k : ℕ) :
    kpTerm P H M δ k = clusterTerm (incP P) (fun Z => ‖H Z‖ * Real.exp ((9 * Real.log 2 + δ) * Z.1.card))
      ((Finset.univ : Finset P).filter fun Z => NotSim Z.1 M) k := by
  unfold kpTerm clusterTerm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun Z _ => ?_
  have hiff : (∃ i, NotSim (Z i).1 M) ↔ ∃ i, Z i ∈ (Finset.univ : Finset P).filter fun Z => NotSim Z.1 M := by
    simp
  by_cases h : ∃ i, NotSim (Z i).1 M
  · rw [if_pos h, if_pos (hiff.1 h)]
    unfold phiT clCard
    rw [norm_mul, norm_mul, norm_inv, Complex.norm_natCast, Complex.norm_intCast, norm_prod, two_pow_eq_exp,
      ← Real.exp_add]
    push_cast
    rw [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    congr 1
    · ring_nf
  · rw [if_neg h, if_neg (fun h' => h (hiff.2 h')), mul_zero]

/-- **`lem:fluctuation-kp`(ii)**, with a weight `e^{δ#}` (`δ = 0` is (ii), `δ = 1` is the form of (iv)): the series
`Σ_{𝒞 ≁ M}|φ^T(𝒞)|2^{9#(𝒞)}e^{δ#(𝒞)}`, summed over the number of polymers, converges and is at most `c#(M)`, for
`0 ≤ |H(Z)| ≤ e^{-5κ}e^{-κd(Z)}` and `κ ≥ 2⁹(1 + δ + 16 log 2)`. -/
theorem fluctuation_kp_ii (P : Finset (Finset (Cube N))) (hP : ∀ Z ∈ P, IsConn Z) {κ δ : ℝ} (hδ : 0 ≤ δ)
    (hκ : 2 ^ 9 * (1 + δ + 16 * Real.log 2) ≤ κ) (H : P → ℂ)
    (hH : ∀ Z, ‖H Z‖ ≤ Real.exp (-5 * κ) * Real.exp (-κ * size s N Z.1)) (M : Finset (Cube N)) :
    Summable (kpTerm P H M δ) ∧ ∑' k, kpTerm P H M δ k ≤ cKP κ * M.card := by
  have hcrit := fun M' => kp_weighted hs P hP hδ hκ (fun Z => ‖H Z‖) (fun Z => norm_nonneg _) hH M'
  have hb := cluster_bound (inc := incP P) (fun Z => notSim_refl (hP Z.1 Z.2).nonempty)
    (fun Z Z' h => notSim_symm h) (fun Z => ‖H Z‖) (fun Z => (9 * Real.log 2 + δ) * Z.1.card)
    (fun Z => cKP κ * Z.1.card) (fun Z => norm_nonneg _)
    (fun Z => by
      have := hcrit Z.1
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun Z' _ => ?_)) this
      rfl)
    ((Finset.univ : Finset P).filter fun Z => NotSim Z.1 M) (cKP κ * M.card) (hcrit M)
  have e : kpTerm P H M δ = clusterTerm (incP P) (fun Z => ‖H Z‖ * Real.exp ((9 * Real.log 2 + δ) * Z.1.card))
      ((Finset.univ : Finset P).filter fun Z => NotSim Z.1 M) := funext fun k => kpTerm_eq P H M δ k
  rw [e]
  exact ⟨hb.1, hb.2.1.trans hb.2.2⟩

/-- **`lem:fluctuation-kp`(iii)**: for any subfamily `𝒫'` of `𝒫` (the polymers compatible with `M`, or all), the sum of
`Π_iH(Z_i)` over the finite sets of pairwise compatible polymers of `𝒫'` is `exp Σ_𝒞φ^T(𝒞)` over the clusters formed
from `𝒫'`, the series (summed over the number of polymers) converging absolutely. -/
theorem fluctuation_kp_iii (P : Finset (Finset (Cube N))) (hP : ∀ Z ∈ P, IsConn Z) {κ : ℝ} (hκ : kappaVac ≤ κ)
    (H : P → ℂ) (hH : ∀ Z, ‖H Z‖ ≤ Real.exp (-5 * κ) * Real.exp (-κ * size s N Z.1)) (p : P → Prop) :
    Summable (fun k => ‖logTerm (fun Z Z' : {Z : P // p Z} => incP P Z.1 Z'.1) (fun Z => H Z.1) k‖) ∧
      Cluster.Xi (fun Z Z' : {Z : P // p Z} => incP P Z.1 Z'.1) Finset.univ (fun Z => H Z.1) =
        Complex.exp (∑' k, logTerm (fun Z Z' : {Z : P // p Z} => incP P Z.1 Z'.1) (fun Z => H Z.1) k) := by
  set inc' := fun Z Z' : {Z : P // p Z} => incP P Z.1 Z'.1 with hinc'
  have hrefl : ∀ Z, inc' Z Z := fun Z => notSim_refl (hP Z.1.1 Z.1.2).nonempty
  have hsymm : ∀ Z Z', inc' Z Z' → inc' Z' Z := fun Z Z' h => notSim_symm h
  set w : {Z : P // p Z} → ℝ := fun Z => ‖H Z.1‖ with hw
  set a : {Z : P // p Z} → ℝ := fun Z => cKP κ * Z.1.1.card with ha
  have hcrit := fun M' => kp_weighted hs P hP le_rfl (by unfold kappaVac at hκ; linarith) (fun Z => ‖H Z‖)
    (fun Z => norm_nonneg _) hH M'
  have hKP : Cluster.KP inc' Finset.univ w a := by
    intro Z _
    have h := hcrit Z.1.1
    refine le_trans ?_ h
    -- the subfamily's sum is a part of the full sum, with the factor `2^{9#} ≥ 1` dropped
    calc ∑ Z' ∈ (Finset.univ : Finset {Z : P // p Z}).filter (fun Z' => inc' Z' Z), w Z' * Real.exp (a Z')
        = ∑ Z' ∈ ((Finset.univ : Finset {Z : P // p Z}).filter (fun Z' => inc' Z' Z)).map
            (Function.Embedding.subtype p), ‖H Z'‖ * Real.exp (cKP κ * Z'.1.card) := by
          rw [Finset.sum_map]; rfl
      _ ≤ ∑ Z' ∈ (Finset.univ : Finset P).filter (fun Z' => NotSim Z'.1 Z.1.1),
            ‖H Z'‖ * Real.exp (cKP κ * Z'.1.card) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun Z' hZ' => ?_) fun _ _ _ => by positivity
          obtain ⟨Z'', hZ'', rfl⟩ := Finset.mem_map.1 hZ'
          exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hZ'').2⟩
      _ ≤ _ := Finset.sum_le_sum fun Z' _ => by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _)
          have : 0 ≤ (9 * Real.log 2 + 0) * (Z'.1.card : ℝ) := by have := log_two_pos; positivity
          linarith
  obtain ⟨-, L, -, -, hLe, habs, hLs⟩ := polymer_log hrefl hsymm w a (fun Z => norm_nonneg _) hKP
    (fun Z => H Z.1) (fun Z => le_rfl)
  refine ⟨habs, ?_⟩
  have h1 := hLe 1 ⟨zero_le_one, le_rfl⟩
  simp only [Complex.ofReal_one, one_mul] at h1
  rw [← h1, hLs.tsum_eq]

/-- **`lem:fluctuation-kp`(iv)**: for activities `H_t` depending on a parameter `t ∈ T` with
`|H_t(Z)| ≤ e^{-5κ}e^{-κd(Z)}` on `T` and `κ ≥ 2⁹(2 + 16 log 2)`, the suprema `H̄(Z) = sup_t|H_t(Z)|` satisfy (i) and (ii)
with the weight `2^{9#}e^{#}`, and `|φ_t^T(𝒞)| ≤ φ̄(𝒞) = (1/n!)|ρ^T|H̄(Z_1)⋯H̄(Z_n)`. -/
theorem fluctuation_kp_iv (P : Finset (Finset (Cube N))) (hP : ∀ Z ∈ P, IsConn Z) {κ : ℝ}
    (hκ : 2 ^ 9 * (2 + 16 * Real.log 2) ≤ κ) {T : Type*} (H : T → P → ℂ)
    (hH : ∀ t Z, ‖H t Z‖ ≤ Real.exp (-5 * κ) * Real.exp (-κ * size s N Z.1)) (M : Finset (Cube N)) :
    let Hb : P → ℝ := fun Z => ⨆ t, ‖H t Z‖
    ∑ Z ∈ (Finset.univ : Finset P).filter (fun Z => NotSim Z.1 M),
        Hb Z * Real.exp (cKP κ * Z.1.card) * 2 ^ (9 * Z.1.card) * Real.exp (Z.1.card) ≤ cKP κ * M.card ∧
      Summable (kpTerm P (fun Z => (Hb Z : ℂ)) M 1) ∧ ∑' k, kpTerm P (fun Z => (Hb Z : ℂ)) M 1 k ≤ cKP κ * M.card ∧
      ∀ (t : T) {n : ℕ} (Z : Fin n → P), ‖phiT P (H t) Z‖ ≤ ‖phiT P (fun Z => (Hb Z : ℂ)) Z‖ := by
  intro Hb
  have hbdd : ∀ Z, BddAbove (Set.range fun t => ‖H t Z‖) := fun Z =>
    ⟨_, by rintro _ ⟨t, rfl⟩; exact hH t Z⟩
  have hHb0 : ∀ Z, 0 ≤ Hb Z := fun Z => Real.iSup_nonneg fun t => norm_nonneg _
  have hHb : ∀ Z, Hb Z ≤ Real.exp (-5 * κ) * Real.exp (-κ * size s N Z.1) := fun Z =>
    Real.iSup_le (fun t => hH t Z) (by positivity)
  have hHbC : ∀ Z, ‖((Hb Z : ℝ) : ℂ)‖ ≤ Real.exp (-5 * κ) * Real.exp (-κ * size s N Z.1) := fun Z => by
    rw [Complex.norm_real, Real.norm_of_nonneg (hHb0 Z)]; exact hHb Z
  have hκ1 : 2 ^ 9 * (1 + 1 + 16 * Real.log 2) ≤ κ := by linarith
  refine ⟨?_, (fluctuation_kp_ii hs P hP zero_le_one hκ1 _ hHbC M).1,
    (fluctuation_kp_ii hs P hP zero_le_one hκ1 _ hHbC M).2, fun t n Z => ?_⟩
  · have h := kp_weighted hs P hP zero_le_one hκ1 Hb hHb0 hHb M
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun Z _ => ?_)) h
    rw [two_pow_eq_exp, mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
    ring_nf
  · unfold phiT
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_prod, norm_prod]
    refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_)
      (by positivity)
    rw [Complex.norm_real, Real.norm_of_nonneg (hHb0 _)]
    exact le_ciSup (hbdd _) t

end PolymerGrid
end CoreLean

end
