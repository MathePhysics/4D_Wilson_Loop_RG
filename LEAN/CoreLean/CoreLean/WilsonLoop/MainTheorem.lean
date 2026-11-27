import CoreLean.WilsonLoop.Statement

/-!
# Theorem 1.5 of [WL] (Uniform Bound and Limit)

The construction and its estimates remain to be formalised in `existsBalabanRG`.
The uniform bound and nonvanishing below use the same chosen construction.
-/

noncomputable section

namespace CoreLean
namespace WilsonLoop

variable {N : ℕ}

/-- The construction for [WL] Theorem 1.5 and its Nonvanishing proposition. -/
theorem existsBalabanRG (G : GaugeGroup N) [CompactSpace G.carrier]
    (hconn : IsConnected (G.carrier : Set (Matrix (Fin N) (Fin N) ℂ)ˣ)) (hsimple : G.IsSimple) :
    ∃ L₀ : ℝ → ℕ, ∀ (Λstar : ℝ) (L : ℕ) [NeZero L],
      2 ≤ Λstar → Odd L → L₀ Λstar ≤ L →
      ∃ rg : RGConstruction G L, BoundAndLimit rg Λstar ∧ Nonvanishing rg Λstar := by
  sorry

variable (G : GaugeGroup N) [CompactSpace G.carrier]
variable (hconn : IsConnected (G.carrier : Set (Matrix (Fin N) (Fin N) ℂ)ˣ)) (hsimple : G.IsSimple)

/-- The required blocking factor for a given bound on loop shapes. -/
def blockingThreshold : ℝ → ℕ :=
  Classical.choose (existsBalabanRG G hconn hsimple)

/-- The construction at an admissible blocking factor and shape bound. -/
def balabanRG (Λstar : ℝ) (L : ℕ) [NeZero L] (hΛ : 2 ≤ Λstar) (hOdd : Odd L)
    (hL : blockingThreshold G hconn hsimple Λstar ≤ L) :
    {rg : RGConstruction G L // BoundAndLimit rg Λstar ∧ Nonvanishing rg Λstar} := by
  have h := Classical.choose_spec (existsBalabanRG G hconn hsimple) Λstar L hΛ hOdd hL
  exact ⟨Classical.choose h, Classical.choose_spec h⟩

/-- **Theorem 1.5 of [WL]** (Uniform Bound and Limit). -/
theorem boundAndLimit (Λstar : ℝ) (L : ℕ) [NeZero L] (hΛ : 2 ≤ Λstar) (hOdd : Odd L)
    (hL : blockingThreshold G hconn hsimple Λstar ≤ L) :
    BoundAndLimit (balabanRG G hconn hsimple Λstar L hΛ hOdd hL).val Λstar :=
  (balabanRG G hconn hsimple Λstar L hΛ hOdd hL).property.1

/-- The Nonvanishing proposition of [WL], for the same RG construction. -/
theorem nonvanishing (Λstar : ℝ) (L : ℕ) [NeZero L] (hΛ : 2 ≤ Λstar) (hOdd : Odd L)
    (hL : blockingThreshold G hconn hsimple Λstar ≤ L) :
    Nonvanishing (balabanRG G hconn hsimple Λstar L hΛ hOdd hL).val Λstar :=
  (balabanRG G hconn hsimple Λstar L hΛ hOdd hL).property.2

private theorem MainBound.later {W : ℕ → ℂ} {J₀ J₁ : ℕ} {B : ℝ}
    (h : MainBound W J₀ B) (hJ : J₀ ≤ J₁) : MainBound W J₁ B := by
  refine ⟨fun K hK ↦ h.1 K (hJ.trans hK), ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hJ
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using (summable_nat_add_iff d).2 h.2

/-- The original existential statement follows from the two results, with the later of
their starting cutoffs for each ensemble. -/
theorem existentialBoundAndLimit
    (hconn : IsConnected (G.carrier : Set (Matrix (Fin N) (Fin N) ℂ)ˣ)) (hsimple : G.IsSimple) :
    ExistentialBoundAndLimit G := by
  obtain ⟨L₀, h⟩ := existsBalabanRG G hconn hsimple
  refine ⟨L₀, ?_⟩
  intro Λstar L _ hΛ hOdd hL
  obtain ⟨rg, hb, hn⟩ := h Λstar L hΛ hOdd hL
  refine ⟨rg.constants, fun mT ↦ ?_⟩
  obtain ⟨nv, hn⟩ := hn mT
  refine ⟨nv, fun gbar hg hg' ↦ ?_⟩
  obtain ⟨_, hwin, hb⟩ := hb mT gbar hg hg'
  refine ⟨rg.bareCoupling mT gbar, rg.coefficients gbar, hwin, fun q hq ↦ ?_⟩
  obtain ⟨J₀, B, hb⟩ := hb q hq
  have hstop := rg.level_le_stoppingIndex gbar q hg hg'
  by_cases hsmall : gbar ≤ (nv q).gbar₁
  · obtain ⟨J₁, hn⟩ := hn gbar hg hg' q hq hsmall
    refine ⟨fun d ↦ max (J₀ d) (J₁ d), B, fun E hE ↦ ⟨?_, ?_⟩⟩
    · intro hlevel
      obtain ⟨hj, hB⟩ := hb E hE hlevel
      have hmax : J₀ E.data ≤ max (J₀ E.data) (J₁ E.data) := le_max_left _ _
      refine ⟨hstop.trans (hj.le.trans hmax), ?_⟩
      simpa only [MainBound, RGConstruction.renormExpect_eq] using hB.later hmax
    · intro _ hD hlen
      obtain ⟨hlevel, _, hmin⟩ := hn E hE hD hlen
      refine ⟨hlevel, fun K hK ↦ ?_⟩
      have hmax : J₁ E.data ≤ max (J₀ E.data) (J₁ E.data) := le_max_right _ _
      simpa only [RGConstruction.renormExpect_eq] using hmin K (hmax.trans hK)
  · refine ⟨J₀, B, fun E hE ↦ ⟨?_, ?_⟩⟩
    · intro hlevel
      obtain ⟨hj, hB⟩ := hb E hE hlevel
      exact ⟨hstop.trans hj.le,
        by simpa only [MainBound, RGConstruction.renormExpect_eq] using hB⟩
    · intro hg₁
      exact (hsmall hg₁).elim

end WilsonLoop
end CoreLean
