import GaussianBlockSpin.KruskalForests
import GaussianBlockSpin.PowerCountingOrderings

/-! **The spatial sum for a fixed ordering** (the first estimate (2.13)-(2.14) of III with the localisation sums):
for a connected multigraph, line weights `w_l ≤ 1` with `∫ w_l(y, ·) dν ≤ B_l`, `∫ w_l(·, y) dν ≤ B_l`, and a root
`v₀` integrated over a set of measure at most one, the integral over all positions of `∏_l w_l` is at most the product
of `B_l` over the tree lines of any ordering (lmarginal_lines_le_treeLines). -/

namespace GaussianBlockSpin

open MeasureTheory MergeTree
open scoped ENNReal

variable {V E X : Type*} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E] [MeasurableSpace X]
  [MeasurableSingletonClass X] [Countable X] {ν : Measure X} [SigmaFinite ν] {ends : E → V × V}

/-- **The spatial sum for a fixed ordering.** -/
theorem lmarginal_lines_le_treeLines (hconn : ∀ u v, lineConn ends (Finset.univ : Finset E).toList u v)
    (σ : Fin (Fintype.card E) ≃ E) (w : E → X → X → ℝ≥0∞) (hw1 : ∀ l x y, w l x y ≤ 1) (B : E → ℝ≥0∞)
    (hB₁ : ∀ l y, ∫⁻ x', w l y x' ∂ν ≤ B l) (hB₂ : ∀ l y, ∫⁻ x', w l x' y ∂ν ≤ B l) (v₀ : V) (box : Set X)
    (hbox : ν box ≤ 1) (x₀ : V → X) :
    (∫⋯∫⁻_(Finset.univ), (fun x => box.indicator 1 (x v₀) * ∏ l, w l (x (ends l).1) (x (ends l).2))
      ∂(fun _ => ν)) x₀ ≤ ((treeLines ends (List.ofFn σ)).map B).prod := by
  have hconnσ : ∀ u v, lineConn ends (List.ofFn σ) u v := fun u v =>
    lineConn_mono (fun l _ => List.mem_ofFn.mpr ⟨σ.symm l, by simp⟩) (hconn u v)
  obtain ⟨t, hwf, hverts, hlines⟩ := exists_kruskal_tree hconnσ v₀
  have hnd : t.lines.Nodup :=
    hlines.nodup_iff.mpr ((treeLines_sublist ends _).nodup (List.nodup_ofFn.mpr σ.injective))
  -- the lines outside the tree are dropped
  have hprod : ∀ x : V → X, ∏ l, w l (x (ends l).1) (x (ends l).2) ≤ treeWeight ends w t x := by
    intro x
    set f := fun l => w l (x (ends l).1) (x (ends l).2) with hf
    have hsub : t.lines.toFinset ⊆ Finset.univ := Finset.subset_univ _
    rw [← Finset.prod_sdiff hsub]
    have h1 : ∏ l ∈ Finset.univ \ t.lines.toFinset, f l ≤ 1 :=
      Finset.prod_le_one fun l _ => hw1 _ _ _
    calc (∏ l ∈ Finset.univ \ t.lines.toFinset, f l) * ∏ l ∈ t.lines.toFinset, f l
        ≤ 1 * ∏ l ∈ t.lines.toFinset, f l := mul_le_mul_of_nonneg_right h1 bot_le
      _ = treeWeight ends w t x := by rw [one_mul, List.prod_toFinset _ hnd]; rfl
  have hv₀ : v₀ ∈ t.verts := by rw [hverts]; exact Finset.mem_univ _
  have hmeas : MeasurableSet box := (Set.to_countable box).measurableSet
  calc (∫⋯∫⁻_(Finset.univ), (fun x => box.indicator 1 (x v₀) * ∏ l, w l (x (ends l).1) (x (ends l).2))
        ∂(fun _ => ν)) x₀
      ≤ (∫⋯∫⁻_(Finset.univ), (fun x => box.indicator 1 (x v₀) * treeWeight ends w t x) ∂(fun _ => ν)) x₀ :=
        lmarginal_mono (fun x => mul_le_mul_of_nonneg_left (hprod x) bot_le) x₀
    _ = ∫⁻ z, (∫⋯∫⁻_(Finset.univ.erase v₀), (fun x => box.indicator 1 (x v₀) * treeWeight ends w t x)
          ∂(fun _ => ν)) (Function.update x₀ v₀ z) ∂ν := by
        rw [← Finset.insert_erase (Finset.mem_univ v₀), lmarginal_insert _ (measurable_of_countable _)
          (Finset.notMem_erase v₀ _), Finset.insert_erase (Finset.mem_univ v₀)]
    _ ≤ ∫⁻ z, box.indicator 1 z * treeBound B t ∂ν := by
        refine lintegral_mono fun z => ?_
        have hc : DependsOn (fun x : V → X => box.indicator (1 : X → ℝ≥0∞) (x v₀))
            (((Finset.univ.erase v₀ : Finset V) : Set V)ᶜ) := by
          intro x y hxy
          show box.indicator (1 : X → ℝ≥0∞) (x v₀) = box.indicator 1 (y v₀)
          rw [hxy v₀ (by simp)]
        rw [lmarginal_mul_left_of_dependsOn ν hc (measurable_of_countable _)]
        simp only [Function.update_self]
        refine mul_le_mul_of_nonneg_left ?_ bot_le
        have h := lmarginal_tree_le hB₁ hB₂ t hwf v₀ hv₀ (Function.update x₀ v₀ z)
        rwa [hverts] at h
    _ = treeBound B t * ν box := by
        rw [lintegral_mul_const _ (measurable_of_countable _), lintegral_indicator_one hmeas, mul_comm]
    _ ≤ treeBound B t * 1 := mul_le_mul_of_nonneg_left hbox bot_le
    _ = ((treeLines ends (List.ofFn σ)).map B).prod := by
        rw [mul_one, treeBound]
        exact (hlines.map B).prod_eq

end GaussianBlockSpin
