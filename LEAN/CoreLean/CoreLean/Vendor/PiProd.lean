/-
Products of absolutely summable families over a finite power: the sum over all tuples of the
product is the product of the sums (`Balaban.Green.pi_prod_summable_hasSum`).

Provenance: the section `PiProd` (lines 46-126) of `Balaban/Green/KF0WalkOrdinary.lean` of
https://github.com/scottnarmstrong/balaban-lean at commit `493e9eb`, Apache License 2.0
(`LICENSE-balaban-lean`); the imports are the Mathlib imports of that file, and
`piProdStmt_option` is given a larger heartbeat budget, which it needs outside the module system.
-/
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.RCLike.Basic

namespace Balaban.Green

open Finset Filter Topology

/-! ### Products of summable families over a finite power -/

section PiProd

variable {𝕜 : Type} [RCLike 𝕜] {κ : Type}

/-- The statement of `pi_prod_summable_hasSum` for one index type. -/
def PiProdStmt (𝕜 : Type) [RCLike 𝕜] (κ : Type) (ι : Type) [Fintype ι] : Prop :=
  ∀ (f : ι → κ → 𝕜), (∀ i, Summable fun k => ‖f i k‖) →
    Summable (fun τ : ι → κ => ∏ i, ‖f i (τ i)‖) ∧
    HasSum (fun τ : ι → κ => ∏ i, f i (τ i)) (∏ i, ∑' k, f i k)

theorem piProdStmt_equiv {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β)
    (ih : PiProdStmt 𝕜 κ α) : PiProdStmt 𝕜 κ β := by
  intro f hf
  obtain ⟨h1, h2⟩ := ih (fun i => f (e i)) (fun i => hf (e i))
  let E : (β → κ) ≃ (α → κ) := Equiv.arrowCongr e.symm (Equiv.refl κ)
  have hE : ∀ τ, E τ = τ ∘ e := fun τ => by
    ext i; simp [E, Equiv.arrowCongr]
  have c1 : (fun τ : β → κ => ∏ i, ‖f i (τ i)‖) =
      (fun σ : α → κ => ∏ i, ‖f (e i) (σ i)‖) ∘ E := by
    ext τ
    simp only [Function.comp, hE]
    exact (Equiv.prod_comp e (fun j => ‖f j (τ j)‖)).symm
  have c2 : (fun τ : β → κ => ∏ i, f i (τ i)) =
      (fun σ : α → κ => ∏ i, f (e i) (σ i)) ∘ E := by
    ext τ
    simp only [Function.comp, hE]
    exact (Equiv.prod_comp e (fun j => f j (τ j))).symm
  refine ⟨?_, ?_⟩
  · rw [c1]; exact E.summable_iff.2 h1
  · rw [c2, E.hasSum_iff, ← Equiv.prod_comp e (fun j => ∑' k, f j k)]; exact h2

theorem piProdStmt_empty : PiProdStmt 𝕜 κ PEmpty := by
  intro f _
  have : Unique (PEmpty → κ) := Pi.uniqueOfIsEmpty _
  refine ⟨?_, ?_⟩
  · simp only [Finset.univ_eq_empty, Finset.prod_empty]; exact Summable.of_finite
  · simp

set_option maxHeartbeats 1000000 in
theorem piProdStmt_option {ι : Type} [Fintype ι] (ih : PiProdStmt 𝕜 κ ι) :
    PiProdStmt 𝕜 κ (Option ι) := by
  intro f hf
  obtain ⟨h1, h2⟩ := ih (fun i => f (some i)) (fun i => hf (some i))
  let E : (Option ι → κ) ≃ κ × (ι → κ) :=
    Equiv.piOptionEquivProd (β := fun _ : Option ι => κ)
  have hE : ∀ τ, E τ = (τ none, fun i => τ (some i)) := fun τ => rfl
  have hn : Summable (fun p : κ × (ι → κ) => ‖f none p.1‖ * ∏ i, ‖f (some i) (p.2 i)‖) :=
    Summable.mul_of_nonneg (hf none) h1 (fun _ => norm_nonneg _)
      (fun _ => Finset.prod_nonneg fun _ _ => norm_nonneg _)
  have c1 : (fun τ : Option ι → κ => ∏ i, ‖f i (τ i)‖) =
      (fun p : κ × (ι → κ) => ‖f none p.1‖ * ∏ i, ‖f (some i) (p.2 i)‖) ∘ E := by
    ext τ
    simp only [Function.comp, hE]
    rw [Fintype.prod_option]
  have c2 : (fun τ : Option ι → κ => ∏ i, f i (τ i)) =
      (fun p : κ × (ι → κ) => f none p.1 * ∏ i, f (some i) (p.2 i)) ∘ E := by
    ext τ
    simp only [Function.comp, hE]
    rw [Fintype.prod_option]
  have hs : Summable (fun p : κ × (ι → κ) => f none p.1 * ∏ i, f (some i) (p.2 i)) := by
    refine Summable.of_norm (hn.congr fun p => ?_)
    simp [norm_mul, norm_prod]
  have hv : (∑' p : κ × (ι → κ), f none p.1 * ∏ i, f (some i) (p.2 i)) =
      (∑' k, f none k) * ∏ i, ∑' k, f (some i) k := by
    rw [← h2.tsum_eq]
    symm
    refine tsum_mul_tsum_of_summable_norm (hf none) ?_
    exact h1.congr fun σ => by simp [norm_prod]
  refine ⟨?_, ?_⟩
  · rw [c1]; exact E.summable_iff.2 hn
  · rw [c2, E.hasSum_iff, Fintype.prod_option]
    rw [← hv]; exact hs.hasSum

/-- Absolutely summable families multiply over `ι → κ`: the sum over all tuples of the product
is the product of the sums, and the family of products of norms is summable. -/
theorem pi_prod_summable_hasSum (ι : Type) [Fintype ι] : PiProdStmt 𝕜 κ ι :=
  Fintype.induction_empty_option (P := fun (ι : Type) _ => PiProdStmt 𝕜 κ ι)
    (fun α β _ e ih => @piProdStmt_equiv 𝕜 _ κ α β (Fintype.ofEquiv β e.symm) _ e ih) piProdStmt_empty
    (fun _ _ ih => piProdStmt_option ih) ι

end PiProd

end Balaban.Green
