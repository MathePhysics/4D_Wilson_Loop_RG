/-
`lem:sf-two-layers` of BALABAN_CORE.tex (`a5545dd8c0af`), eq:sf-two-layers-gauge, on the fine lattice at the trivial
configuration with the torus as the Dirichlet domain: for a sequence `S` with the layers `j` and `j + 1` only and every
`λ ∈ N(Q')`, `‖P∂^*A‖² ≤ C_ol(‖∂A‖² + a_j²Σ_{y,μ}|(Q_j(A - ∂λ))(y, μ)|²)`.

* `Pop_DsD_null`: `PD^*Dλ = 0` for `λ ∈ N(Q')`.
* `curl_grad`: `∂∂λ = 0` (the differences of the trivial configuration commute).
* `two_layers_gauge`: eq:sf-two-layers-gauge.
-/
import CoreLean.SFOneLayerFine

open Finset Matrix

noncomputable section

namespace CoreLean
namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFLocal SmallFieldDecay SmallFieldCoercivity
  SequenceOperators CompressedInverse ConcretePairing SFBox SFBox.SeqDomBox

variable (S : SeqDom) {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "NF" => SequenceAverages.N0 S

/-- **`PD^*Dλ = 0` for `λ ∈ N(Q')`** (torus as the Dirichlet domain, trivial configuration). -/
theorem Pop_DsD_null [NeZero N] {lam : Site NF → Mat} (hlam : ∀ y ∈ detB S.toDomSeq, avgW S.toDomSeq (W1 S) y lam = 0) :
    Pop S (X0 S) (W1 S) Set.univ (Ds1L a1 (cfgX (X0 S)) (D0L a1 (cfgX (X0 S)) lam)) = 0 := by
  refine (Pop_eq_zero_iff S _ _ _ (hb_triv (S := S) Set.univ) _).2 ?_
  rw [Gp_null S (X0 S) (W1 S) Set.univ (hK_triv S Set.univ) (piD_univ S lam) hlam]
  exact (blk_zero_iff S (W1 S) lam).2 hlam

lemma D0L_triv (lam : Site NF → Mat) (ν : Fin 4) (x : Site NF) :
    D0L a1 (cfgX (X0 S)) lam ν x = lam (x + unit NF ν) - lam x := by
  simp only [D0L_apply, D0, Dfw, cfgX_X0, Ad_one', a1, Complex.ofReal_one, inv_one, one_smul]

/-- **`∂∂λ = 0`**. -/
lemma curl_grad (lam : Site NF → Mat) (μ ν : Fin 4) (x : Site NF) :
    (D0L a1 (cfgX (X0 S)) lam ν (x + unit NF μ) - D0L a1 (cfgX (X0 S)) lam ν x) -
      (D0L a1 (cfgX (X0 S)) lam μ (x + unit NF ν) - D0L a1 (cfgX (X0 S)) lam μ x) = 0 := by
  simp only [D0L_triv]
  rw [add_right_comm x (unit NF μ) (unit NF ν)]
  abel

/-- **eq:sf-two-layers-gauge.** -/
theorem two_layers_gauge [NeZero N] {j : ℕ} (hj0 : j ≤ S.k) (hj1 : j + 1 ≤ S.k) (hlow : ∀ i ≤ j, S.Ω i = Set.univ)
    (hhigh : ∀ i, j + 2 ≤ i → S.Ω i = ∅) (A : Fin 4 → Site NF → Mat) {lam : Site NF → Mat}
    (hlam : ∀ y ∈ detB S.toDomSeq, avgW S.toDomSeq (W1 S) y lam = 0) :
    ∑ x, hs2 (Pop S (X0 S) (W1 S) Set.univ (Ds1L a1 (cfgX (X0 S)) A) x) ≤
      SFOneLayer.Col * (∑ x, 1 / 2 * ∑ μ, ∑ ν, hs2 ((A ν (x + unit NF μ) - A ν x) - (A μ (x + unit NF ν) - A μ x)) +
        ((S.L ^ j : ℕ) : ℝ) ^ 2 * ∑ y ∈ detB (oneLayer S j hj0).toDomSeq, ∑ μ,
          hs2 (Qt (oneLayer S j hj0) (A - D0L a1 (cfgX (X0 S)) lam) j y μ)) := by
  set A' := A - D0L a1 (cfgX (X0 S)) lam
  -- `P∂^*A = P∂^*(A - ∂λ)`
  have hP : Pop S (X0 S) (W1 S) Set.univ (Ds1L a1 (cfgX (X0 S)) A) =
      Pop S (X0 S) (W1 S) Set.univ (Ds1L a1 (cfgX (X0 S)) A') := by
    rw [map_sub, map_sub, Pop_DsD_null S hlam, sub_zero]
  -- the curl of `A - ∂λ` is that of `A`
  have hc : ∀ x μ ν, (A' ν (x + unit NF μ) - A' ν x) - (A' μ (x + unit NF ν) - A' μ x) =
      (A ν (x + unit NF μ) - A ν x) - (A μ (x + unit NF ν) - A μ x) := fun x μ ν => by
    have := curl_grad S lam μ ν x
    simp only [A', Pi.sub_apply]
    rw [← sub_eq_zero, ← neg_eq_zero, ← this]
    abel
  rw [hP]
  refine (Pop_two_le_one S hj0 hj1 hlow hhigh (hb_triv (S := oneLayer S j hj0) Set.univ)
    (hb_triv (S := S) Set.univ) _).trans ?_
  have h1 := sf_one_layer (S := S) hj0 A'
  simp only [hc] at h1
  exact h1

end SFBounds
end CoreLean

end
