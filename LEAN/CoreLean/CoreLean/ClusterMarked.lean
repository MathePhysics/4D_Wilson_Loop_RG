/-
`lem:marked-expansion` of BALABAN_CORE.tex (`a021c13be348`), in part. On the grid of `ClusterFluct.lean`, for vacuum
activities `H` with `|H(Z)| ≤ e^{-5κ}e^{-κd(Z)}`, `κ ≥ κ_vac`, and a finite family `𝔐` of unions of cubes:
`Ξ(𝔐)`, the polymer sum over the polymers compatible with every member of `𝔐`, satisfies `Ξ(∅) ≠ 0` and
`Ξ(𝔐)/Ξ(∅) = Q(𝔐)Π_{M ∈ 𝔐}e^{-Ψ(M)}`, with `Ψ(M) = Σ_{𝒞 ≁ M}φ^T(𝒞)`, `Ψ_≥(T) = Σ_{𝒞 ≁ M ∀M ∈ T}φ^T(𝒞)`,
`Q(𝔐) = exp Σ_{T ⊆ 𝔐, #T ≥ 2}(-1)^{#T}Ψ_≥(T)`, the series absolutely convergent (`marked_ratio`); hence, for
`I = Σ_𝔐c(𝔐)Ξ(𝔐)`, the representation which `lem:fluctuation-identity`(iv) gives, `I/I_∅ = Σ_𝔐Q(𝔐)Π_Me^{-Ψ(M)}c(𝔐)`
(`marked_expansion`). The proof is the core's: `lem:fluctuation-kp`(iii) for `Ξ(𝔐)` and `Ξ(∅)`, and the
inclusion–exclusion over the members of `𝔐` with which a cluster is incompatible.
-/
import CoreLean.ClusterFluct

open Finset

noncomputable section

namespace CoreLean
namespace PolymerGrid

open Classical
open TreeGraph


variable {s : ℝ} {N : ℕ} [NeZero N]

/-- The terms of a sum over the clusters of `k + 1` polymers with a property `pred`. -/
def clTerm (P : Finset (Finset (Cube N))) (H : P → ℂ) (pred : (k : ℕ) → (Fin (k + 1) → P) → Prop) (k : ℕ) : ℂ :=
  ∑ Z : Fin (k + 1) → P, if pred k Z then phiT P H Z else 0

/-- `Ψ(M) = Σ_{𝒞 ≁ M}φ^T(𝒞)`. -/
def Psi (P : Finset (Finset (Cube N))) (H : P → ℂ) (M : Finset (Cube N)) : ℂ :=
  ∑' k, clTerm P H (fun _ Z => ∃ i, NotSim (Z i).1 M) k

/-- `Ψ_≥(T) = Σ_{𝒞 ≁ M for all M ∈ T}φ^T(𝒞)`. -/
def PsiGe (P : Finset (Finset (Cube N))) (H : P → ℂ) (T : Finset (Finset (Cube N))) : ℂ :=
  ∑' k, clTerm P H (fun _ Z => ∀ M ∈ T, ∃ i, NotSim (Z i).1 M) k

/-- `Q(𝔐) = exp Σ_{T ⊆ 𝔐, #T ≥ 2}(-1)^{#T}Ψ_≥(T)`. -/
def Qm (P : Finset (Finset (Cube N))) (H : P → ℂ) (𝔐 : Finset (Finset (Cube N))) : ℂ :=
  Complex.exp (∑ T ∈ 𝔐.powerset.filter (fun T => 2 ≤ T.card), (-1 : ℂ) ^ T.card * PsiGe P H T)

/-- The polymers compatible with every member of `𝔐`. -/
abbrev Pm (P : Finset (Finset (Cube N))) (𝔐 : Finset (Finset (Cube N))) (Z : P) : Prop := ∀ M ∈ 𝔐, ¬ NotSim Z.1 M

/-- The polymer sum over the polymers with a property `p`. -/
def XiP (P : Finset (Finset (Cube N))) (H : P → ℂ) (p : P → Prop) : ℂ :=
  Cluster.Xi (fun Z Z' : {Z : P // p Z} => incP P Z.1 Z'.1) Finset.univ (fun Z => H Z.1)

/-- `Ξ(𝔐)`. -/
def Xim (P : Finset (Finset (Cube N))) (H : P → ℂ) (𝔐 : Finset (Finset (Cube N))) : ℂ := XiP P H (Pm P 𝔐)

/-- The norm of a cluster term with a property implying `𝒞 ≁ M` is dominated by the term of `lem:fluctuation-kp`(ii). -/
lemma norm_clTerm_le (P : Finset (Finset (Cube N))) (H : P → ℂ) (pred : (k : ℕ) → (Fin (k + 1) → P) → Prop)
    (M : Finset (Cube N)) (hpred : ∀ k Z, pred k Z → ∃ i, NotSim (Z i).1 M) (k : ℕ) :
    ‖clTerm P H pred k‖ ≤ kpTerm P H M 0 k := by
  unfold clTerm kpTerm
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun Z _ => ?_)
  by_cases h : pred k Z
  · rw [if_pos h, if_pos (hpred k Z h), zero_mul, Real.exp_zero, mul_one]
    exact le_mul_of_one_le_right (norm_nonneg _) (one_le_pow₀ (by norm_num))
  · rw [if_neg h, norm_zero]
    split_ifs
    · positivity
    · exact le_rfl

/-- The logarithm of `Ξ(𝔐)` as a sum over the clusters of `𝒫` all of whose polymers have the property `p`. -/
lemma logTerm_sub (P : Finset (Finset (Cube N))) (H : P → ℂ) (p : P → Prop) (k : ℕ) :
    logTerm (fun Z Z' : {Z : P // p Z} => incP P Z.1 Z'.1) (fun Z => H Z.1) k =
      clTerm P H (fun _ Z => ∀ i, p (Z i)) k := by
  set G : (Fin (k + 1) → P) → ℂ := fun Z =>
    (((k + 1).factorial : ℂ))⁻¹ * (ursS (incP P) Z : ℂ) * ∏ i, H (Z i) with hG
  have h1 : logTerm (fun Z Z' : {Z : P // p Z} => incP P Z.1 Z'.1) (fun Z => H Z.1) k =
      ∑ Z' : Fin (k + 1) → {Z : P // p Z}, G (fun i => (Z' i).1) := by
    unfold logTerm Ck Ci
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun Z' _ => ?_
    simp only [hG]
    rw [div_eq_inv_mul, mul_assoc]
    rfl
  rw [h1]
  have h2 : ∑ Z' : Fin (k + 1) → {Z : P // p Z}, G (fun i => (Z' i).1) =
      ∑ f : {f : Fin (k + 1) → P // ∀ i, p (f i)}, G f.1 :=
    Fintype.sum_equiv (Equiv.subtypePiEquivPi).symm _ _ fun Z' => rfl
  rw [h2, ← Finset.sum_subtype (Finset.univ.filter fun f : Fin (k + 1) → P => ∀ i, p (f i)) (by simp),
    Finset.sum_filter]
  unfold clTerm phiT
  refine Finset.sum_congr rfl fun Z _ => ?_
  by_cases h : ∀ i, p (Z i)
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

/-- The binomial count of the inclusion–exclusion: `Σ_{2 ≤ m ≤ n}C(n, m)(-1)^m = [n = 0] - 1 + n`. -/
lemma binom_count (n : ℕ) :
    ∑ m ∈ Finset.range (n + 1), (n.choose m : ℤ) * (if 2 ≤ m then (-1) ^ m else 0) =
      (if n = 0 then 1 else 0) - 1 + n := by
  rcases n with _ | k
  · simp
  · have halt := Int.alternating_sum_range_choose (n := k + 1)
    rw [Finset.sum_range_succ', Finset.sum_range_succ'] at halt ⊢
    simp only [Nat.choose_zero_right, Nat.choose_one_right, pow_zero, pow_one] at halt ⊢
    have e : ∀ m ∈ Finset.range k, ((k + 1).choose (m + 1 + 1) : ℤ) * (if 2 ≤ m + 1 + 1 then (-1) ^ (m + 1 + 1) else 0)
        = (-1) ^ (m + 1 + 1) * ((k + 1).choose (m + 1 + 1) : ℤ) := fun m _ => by
      rw [if_pos (by omega)]; ring
    rw [Finset.sum_congr rfl e]
    simp only [Nat.add_eq_zero, one_ne_zero, and_false, if_false] at halt ⊢
    push_cast at halt ⊢
    norm_num at halt ⊢
    linarith

/-- **The inclusion–exclusion** for one set `S`: `[S ≠ ∅] = #S - Σ_{T ⊆ S, #T ≥ 2}(-1)^{#T}`. -/
lemma incl_excl {α : Type*} (S : Finset α) :
    (if S = ∅ then (0 : ℂ) else 1) = S.card - ∑ T ∈ S.powerset.filter (fun T => 2 ≤ T.card), (-1 : ℂ) ^ T.card := by
  have h := binom_count S.card
  have h2 : ∑ T ∈ S.powerset.filter (fun T => 2 ≤ T.card), (-1 : ℤ) ^ T.card =
      ∑ m ∈ Finset.range (S.card + 1), (S.card.choose m : ℤ) * (if 2 ≤ m then (-1) ^ m else 0) := by
    rw [Finset.sum_filter, Finset.sum_powerset_apply_card (f := fun m => if 2 ≤ m then (-1 : ℤ) ^ m else 0)]
    exact Finset.sum_congr rfl fun m _ => by rw [nsmul_eq_mul]
  have hZ := h2.trans h
  have hc : ∑ T ∈ S.powerset.filter (fun T => 2 ≤ T.card), (-1 : ℂ) ^ T.card =
      ((∑ T ∈ S.powerset.filter (fun T => 2 ≤ T.card), (-1 : ℤ) ^ T.card : ℤ) : ℂ) := by push_cast; rfl
  rw [hc, hZ]
  by_cases hS : S = ∅
  · subst hS; simp
  · have : S.card ≠ 0 := fun h0 => hS (Finset.card_eq_zero.1 h0)
    simp [hS, this]

/-- A sum of a constant over the elements with a property, for any decidability instance. -/
lemma sum_ite_card {β : Type*} (𝔐 : Finset β) (c : β → Prop) {inst : DecidablePred c} (x : ℂ) :
    (∑ M ∈ 𝔐, @ite ℂ (c M) (inst M) x 0) = ((@Finset.filter β c inst 𝔐).card : ℂ) * x := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

/-- The sum over the subsets `T`, `#T ≥ 2`, all of whose members have a property. -/
lemma sum_powerset_ite {β : Type*} (𝔐 : Finset β) (c : β → Prop) {inst : DecidablePred c}
    {inst2 : ∀ T : Finset β, Decidable (∀ M ∈ T, c M)} (x : ℂ) :
    (∑ T ∈ 𝔐.powerset.filter (fun T => 2 ≤ T.card), (-1 : ℂ) ^ T.card * @ite ℂ (∀ M ∈ T, c M) (inst2 T) x 0) =
      (∑ T ∈ (@Finset.filter β c inst 𝔐).powerset.filter (fun T => 2 ≤ T.card), (-1 : ℂ) ^ T.card) * x := by
  rw [Finset.sum_mul]
  simp only [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun T _ => rfl
  ext T
  simp only [Finset.mem_filter, Finset.mem_powerset]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨fun M hM => Finset.mem_filter.2 ⟨h1 hM, h3 M hM⟩, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨fun M hM => (Finset.mem_filter.1 (h1 hM)).1, h2⟩, fun M hM => (Finset.mem_filter.1 (h1 hM)).2⟩

/-- The pointwise identity of the inclusion–exclusion, for any decidability instances. -/
lemma final_id {β : Type*} (𝔐 : Finset β) (c : β → Prop) {inst : DecidablePred c} (φ : ℂ) {d0 d1 : Prop}
    {i0 : Decidable d0} {i1 : Decidable d1} (h0 : d0) (h1 : d1 ↔ ∀ M ∈ 𝔐, ¬ c M) :
    @ite ℂ d0 i0 φ 0 - @ite ℂ d1 i1 φ 0 = ((@Finset.filter β c inst 𝔐).card : ℂ) * φ -
      (∑ T ∈ (@Finset.filter β c inst 𝔐).powerset.filter (fun T => 2 ≤ T.card), (-1 : ℂ) ^ T.card) * φ := by
  have hie := incl_excl (@Finset.filter β c inst 𝔐)
  have hS : (@Finset.filter β c inst 𝔐) = ∅ ↔ d1 := by
    rw [Finset.filter_eq_empty_iff, h1]
  rw [if_pos h0]
  by_cases hS0 : (@Finset.filter β c inst 𝔐) = ∅
  · rw [if_pos (hS.1 hS0)]
    rw [if_pos hS0] at hie
    linear_combination φ * hie
  · rw [if_neg (fun h => hS0 (hS.2 h))]
    rw [if_neg hS0] at hie
    linear_combination φ * hie

/-- The identity of one cluster, for any decidability instances. -/
lemma per_cluster {β : Type*} (𝔐 : Finset β) (c : β → Prop) {inst : DecidablePred c}
    {inst2 : ∀ T : Finset β, Decidable (∀ M ∈ T, c M)} (φ : ℂ) {d0 d1 : Prop} {i0 : Decidable d0}
    {i1 : Decidable d1} (h0 : d0) (h1 : d1 ↔ ∀ M ∈ 𝔐, ¬ c M) :
    @ite ℂ d0 i0 φ 0 - @ite ℂ d1 i1 φ 0 = (∑ M ∈ 𝔐, @ite ℂ (c M) (inst M) φ 0) -
      ∑ T ∈ 𝔐.powerset.filter (fun T => 2 ≤ T.card), (-1 : ℂ) ^ T.card * @ite ℂ (∀ M ∈ T, c M) (inst2 T) φ 0 := by
  rw [sum_ite_card, sum_powerset_ite]
  exact final_id 𝔐 c φ h0 h1

variable (hs : 0 < s)
include hs

/-- **`lem:marked-expansion`, the ratio**: `Ξ(∅) ≠ 0`, the series `Ψ(M)` and `Ψ_≥(T)` (`T ⊆ 𝔐` nonempty) converge
absolutely, and `Ξ(𝔐)/Ξ(∅) = Q(𝔐)Π_{M ∈ 𝔐}e^{-Ψ(M)}`. -/
theorem marked_ratio (P : Finset (Finset (Cube N))) (hP : ∀ Z ∈ P, IsConn Z) {κ : ℝ} (hκ : kappaVac ≤ κ)
    (H : P → ℂ) (hH : ∀ Z, ‖H Z‖ ≤ Real.exp (-5 * κ) * Real.exp (-κ * size s N Z.1))
    (𝔐 : Finset (Finset (Cube N))) :
    Xim P H ∅ ≠ 0 ∧
      (∀ M, Summable fun k => ‖clTerm P H (fun _ Z => ∃ i, NotSim (Z i).1 M) k‖) ∧
      (∀ T : Finset (Finset (Cube N)), T.Nonempty →
        Summable fun k => ‖clTerm P H (fun _ Z => ∀ M ∈ T, ∃ i, NotSim (Z i).1 M) k‖) ∧
      Xim P H 𝔐 / Xim P H ∅ = Qm P H 𝔐 * ∏ M ∈ 𝔐, Complex.exp (-Psi P H M) := by
  have hκ0 : 2 ^ 9 * (1 + 0 + 16 * Real.log 2) ≤ κ := by unfold kappaVac at hκ; linarith
  have hkp : ∀ M, Summable (kpTerm P H M 0) := fun M => (fluctuation_kp_ii hs P hP le_rfl hκ0 H hH M).1
  have hsM : ∀ M, Summable fun k => ‖clTerm P H (fun _ Z => ∃ i, NotSim (Z i).1 M) k‖ := fun M =>
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) (norm_clTerm_le P H _ M (fun _ _ h => h)) (hkp M)
  have hsT : ∀ T : Finset (Finset (Cube N)), T.Nonempty →
      Summable fun k => ‖clTerm P H (fun _ Z => ∀ M ∈ T, ∃ i, NotSim (Z i).1 M) k‖ := by
    intro T ⟨M, hM⟩
    exact Summable.of_nonneg_of_le (fun k => norm_nonneg _)
      (norm_clTerm_le P H _ M (fun _ _ h => h M hM)) (hkp M)
  refine ⟨?_, hsM, hsT, ?_⟩
  · obtain ⟨-, h⟩ := fluctuation_kp_iii hs P hP hκ H hH (Pm P ∅)
    unfold Xim XiP
    rw [h]; exact Complex.exp_ne_zero _
  -- the two logarithms
  obtain ⟨hA, hXA⟩ := fluctuation_kp_iii hs P hP hκ H hH (Pm P ∅)
  obtain ⟨hB, hXB⟩ := fluctuation_kp_iii hs P hP hκ H hH (Pm P 𝔐)
  simp only [logTerm_sub] at hA hB hXA hXB
  have hsA := hA.of_norm.hasSum
  have hsB := hB.of_norm.hasSum
  -- the pointwise identity
  have hpt : ∀ k, clTerm P H (fun _ Z => ∀ i, Pm P ∅ (Z i)) k - clTerm P H (fun _ Z => ∀ i, Pm P 𝔐 (Z i)) k =
      ∑ M ∈ 𝔐, clTerm P H (fun _ Z => ∃ i, NotSim (Z i).1 M) k -
        ∑ T ∈ 𝔐.powerset.filter (fun T => 2 ≤ T.card),
          (-1 : ℂ) ^ T.card * clTerm P H (fun _ Z => ∀ M ∈ T, ∃ i, NotSim (Z i).1 M) k := by
    intro k
    unfold clTerm
    beta_reduce
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    rw [Finset.sum_comm (s := 𝔐), Finset.sum_comm (s := 𝔐.powerset.filter _), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun Z _ => ?_
    exact per_cluster 𝔐 (fun M => ∃ i, NotSim (Z i).1 M) (phiT P H Z)
      (fun i M hM => absurd hM (Finset.notMem_empty M)) (by
      constructor
      · intro h M hM ⟨i, hi⟩; exact h i M hM hi
      · intro h i M hM hi; exact h M hM ⟨i, hi⟩)
  -- summing the identity
  have hlhs := hsA.sub hsB
  have hrhs : HasSum (fun k => ∑ M ∈ 𝔐, clTerm P H (fun _ Z => ∃ i, NotSim (Z i).1 M) k -
      ∑ T ∈ 𝔐.powerset.filter (fun T => 2 ≤ T.card),
        (-1 : ℂ) ^ T.card * clTerm P H (fun _ Z => ∀ M ∈ T, ∃ i, NotSim (Z i).1 M) k)
      (∑ M ∈ 𝔐, Psi P H M - ∑ T ∈ 𝔐.powerset.filter (fun T => 2 ≤ T.card), (-1 : ℂ) ^ T.card * PsiGe P H T) := by
    refine HasSum.sub (hasSum_sum fun M _ => (hsM M).of_norm.hasSum) (hasSum_sum fun T hT => ?_)
    have hT2 := (Finset.mem_filter.1 hT).2
    have hTne : T.Nonempty := Finset.card_pos.1 (by omega)
    exact ((hsT T hTne).of_norm.hasSum).mul_left _
  have hrhs' : HasSum (fun k => clTerm P H (fun _ Z => ∀ i, Pm P ∅ (Z i)) k -
      clTerm P H (fun _ Z => ∀ i, Pm P 𝔐 (Z i)) k)
      (∑ M ∈ 𝔐, Psi P H M - ∑ T ∈ 𝔐.powerset.filter (fun T => 2 ≤ T.card), (-1 : ℂ) ^ T.card * PsiGe P H T) := by
    convert hrhs using 1
    funext k; exact hpt k
  have heq := hlhs.unique hrhs'
  unfold Xim XiP
  rw [hXA, hXB, ← Complex.exp_sub]
  rw [show ∀ a b : ℂ, b - a = -(a - b) from fun a b => by ring, heq, Qm, neg_sub, sub_eq_add_neg,
    Complex.exp_add, ← Finset.sum_neg_distrib, Complex.exp_sum (s := 𝔐)]

/-- **`eq:marked-expansion`**: if `I = Σ_𝔐Ξ(𝔐)c(𝔐)` (the representation of `lem:fluctuation-identity`(iv), with
`c(𝔐) = ⊗_{M ∈ 𝔐}H_{𝔊(M)}(M)` in a complex vector space) and `I_∅ = Ξ(∅)`, then
`I/I_∅ = Σ_𝔐Q(𝔐)Π_{M ∈ 𝔐}e^{-Ψ(M)}c(𝔐)`. -/
theorem marked_expansion (P : Finset (Finset (Cube N))) (hP : ∀ Z ∈ P, IsConn Z) {κ : ℝ} (hκ : kappaVac ≤ κ)
    (H : P → ℂ) (hH : ∀ Z, ‖H Z‖ ≤ Real.exp (-5 * κ) * Real.exp (-κ * size s N Z.1)) {V : Type*}
    [AddCommGroup V] [Module ℂ V] (F : Finset (Finset (Finset (Cube N)))) (c : Finset (Finset (Cube N)) → V) :
    (Xim P H ∅)⁻¹ • ∑ 𝔐 ∈ F, Xim P H 𝔐 • c 𝔐 =
      ∑ 𝔐 ∈ F, (Qm P H 𝔐 * ∏ M ∈ 𝔐, Complex.exp (-Psi P H M)) • c 𝔐 := by
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun 𝔐 _ => ?_
  obtain ⟨h0, -, -, hr⟩ := marked_ratio hs P hP hκ H hH 𝔐
  rw [smul_smul, ← hr, div_eq_inv_mul]

end PolymerGrid
end CoreLean

end
