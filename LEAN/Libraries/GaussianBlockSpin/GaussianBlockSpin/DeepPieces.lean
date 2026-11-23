import GaussianBlockSpin.DecouplingIterate

/-! **Deep pieces from distances**: if `dist` on the coordinates satisfies the triangle inequality, every piece has
diameter at most `R`, and a piece `X` in box `b` has a coordinate `x₀` with `t R < dist(x₀, z)` for every `z ∈ Γ`, then
`X` is deep of order `t ≥ 1` (`Pavement.isDeep_of_dist`). The part `C` around `X` in a tuple is its component in the
graph "two pieces share a coordinate off `Γ`"; walks in it have length `< k ≤ t`, so its pieces lie within `t R` of
`x₀`, avoid `Γ` and stay in the box of `X`. -/

namespace GaussianBlockSpin

open MeasureTheory Function

variable {ι P β : Type*} [Fintype ι] [DecidableEq ι] [Fintype P] [DecidableEq P] [Fintype β] [DecidableEq β]
variable {L : LocalPieces ι P} (pv : Pavement L β)

/-- The overlap graph of a tuple of pieces off the corridors. -/
def Pavement.overlapGraph {k : ℕ} (g : Fin k → P) : SimpleGraph (Fin k) :=
  SimpleGraph.fromRel fun i j => ∃ y ∈ L.supp (g i), y ∈ L.supp (g j) ∧ y ∉ pv.Γ

omit [Fintype ι] [DecidableEq ι] [Fintype P] [DecidableEq P] [Fintype β] [DecidableEq β] in
lemma Pavement.overlapGraph_adj {k : ℕ} {g : Fin k → P} {i j : Fin k} (h : (pv.overlapGraph g).Adj i j) :
    ∃ y ∈ L.supp (g i), y ∈ L.supp (g j) ∧ y ∉ pv.Γ := by
  obtain ⟨-, h | ⟨y, hy1, hy2, hy3⟩⟩ := (SimpleGraph.fromRel_adj _ _ _).mp h
  · exact h
  · exact ⟨y, hy2, hy1, hy3⟩

omit [Fintype ι] [DecidableEq ι] [Fintype P] [DecidableEq P] [Fintype β] [DecidableEq β] in
/-- Along a walk in the overlap graph, the coordinates move by at most `R` per step. -/
lemma Pavement.dist_walk (dist : ι → ι → ℝ) (htri : ∀ x y z, dist x z ≤ dist x y + dist y z) {R : ℝ}
    (hR : ∀ X, ∀ y ∈ L.supp X, ∀ z ∈ L.supp X, dist y z ≤ R) (x₀ : ι) {k : ℕ} (g : Fin k → P) {u v : Fin k}
    (w : (pv.overlapGraph g).Walk u v) :
    ∀ a : ℝ, (∀ y ∈ L.supp (g u), dist x₀ y ≤ a) → ∀ y ∈ L.supp (g v), dist x₀ y ≤ a + w.length * R := by
  induction w with
  | nil => intro a h y hy; simpa using h y hy
  | cons hadj w' ih =>
    intro a h y hy
    obtain ⟨z, hz1, hz2, -⟩ := pv.overlapGraph_adj hadj
    have h1 : ∀ y ∈ L.supp (g _), dist x₀ y ≤ a + R := fun y' hy' =>
      (htri x₀ z y').trans (add_le_add (h z hz1) (hR _ z hz2 y' hy'))
    have := ih (a + R) h1 y hy
    simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one] at this ⊢
    linarith

omit [Fintype ι] [Fintype P] [DecidableEq P] [Fintype β] in
/-- **Deep pieces from distances**. -/
theorem Pavement.isDeep_of_dist (dist : ι → ι → ℝ) (htri : ∀ x y z, dist x z ≤ dist x y + dist y z) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : ∀ X, ∀ y ∈ L.supp X, ∀ z ∈ L.supp X, dist y z ≤ R) {t : ℕ} (ht : 1 ≤ t) {X : P} {b : β}
    (hX : pv.home X = some b) {x₀ : ι} (hx₀ : x₀ ∈ L.supp X) (hfar : ∀ z ∈ pv.Γ, (t : ℝ) * R < dist x₀ z) :
    pv.IsDeep t X := by
  classical
  have htR : R ≤ (t : ℝ) * R := le_mul_of_one_le_left hR0 (by exact_mod_cast ht)
  have hXΓ : Disjoint (L.supp X) pv.Γ := Finset.disjoint_left.mpr fun y hy hyΓ =>
    absurd ((hR X x₀ hx₀ y hy).trans htR) (not_le.mpr (hfar y hyΓ))
  refine ⟨⟨b, hX⟩, hXΓ, fun k hk g i₀ hgi => ?_⟩
  set G := pv.overlapGraph g with hG
  set C := Finset.univ.filter fun i => G.Reachable i₀ i with hC
  -- the pieces of `C` lie within `t R` of `x₀`, hence off `Γ`
  have hnear : ∀ i ∈ C, ∀ y ∈ L.supp (g i), dist x₀ y ≤ (t : ℝ) * R := by
    intro i hi y hy
    obtain ⟨w⟩ := (Finset.mem_filter.mp hi).2
    have hlen : w.bypass.length < k := by
      have := w.bypass_isPath.length_lt
      simpa using this
    have h := pv.dist_walk dist htri hR x₀ g w.bypass R (fun y' hy' => hR X x₀ hx₀ y' (hgi ▸ hy')) y hy
    have hlen' : (w.bypass.length : ℝ) + 1 ≤ t := by
      have : w.bypass.length + 1 ≤ t := by omega
      exact_mod_cast this
    nlinarith
  have hoff : ∀ i ∈ C, Disjoint (L.supp (g i)) pv.Γ := fun i hi => Finset.disjoint_left.mpr fun y hy hyΓ =>
    absurd (hnear i hi y hy) (not_le.mpr (hfar y hyΓ))
  -- adjacent pieces of `C` have the same home
  have hhome_adj : ∀ u v, u ∈ C → v ∈ C → G.Adj u v → pv.home (g u) = pv.home (g v) := by
    intro u v hu hv huv
    obtain ⟨y, hy1, hy2, hyΓ⟩ := pv.overlapGraph_adj huv
    have hbox : ∀ i, y ∈ L.supp (g i) → ∃ c, pv.home (g i) = some c ∧ y ∈ pv.box c := by
      intro i hyi
      cases hh : pv.home (g i) with
      | none => exact absurd (pv.homeNone _ hh hyi) hyΓ
      | some c =>
        refine ⟨c, rfl, ?_⟩
        rcases pv.homeSome _ c hh (Finset.mem_coe.mpr hyi) with h | h
        · exact Finset.mem_coe.mp h
        · exact absurd (Finset.mem_coe.mp h) hyΓ
    obtain ⟨c1, hc1, hyc1⟩ := hbox u hy1
    obtain ⟨c2, hc2, hyc2⟩ := hbox v hy2
    rw [hc1, hc2]
    by_contra hne
    have hne' : c1 ≠ c2 := fun h => hne (by rw [h])
    exact Finset.disjoint_left.mp (pv.disj c1 c2 hne') hyc1 hyc2
  have hhome_walk : ∀ u v (w : G.Walk u v), G.Reachable i₀ u → pv.home (g u) = pv.home (g v) := by
    intro u v w
    induction w with
    | nil => intro _; rfl
    | cons hadj w' ih =>
      intro hu
      have hu' := hu.trans hadj.reachable
      rw [hhome_adj _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu'⟩) hadj]
      exact ih hu'
  refine ⟨C, Finset.mem_filter.mpr ⟨Finset.mem_univ _, SimpleGraph.Reachable.refl _⟩, fun i hi => ⟨hoff i hi, ?_⟩, ?_⟩
  · obtain ⟨w⟩ := (Finset.mem_filter.mp hi).2
    rw [← hgi]
    exact (hhome_walk i₀ i w (SimpleGraph.Reachable.refl _)).symm
  · rw [Finset.disjoint_left]
    intro y hy1 hy2
    obtain ⟨i, hi, hyi⟩ := Finset.mem_biUnion.mp hy1
    obtain ⟨i', hi', hyi'⟩ := Finset.mem_biUnion.mp hy2
    obtain ⟨hyi', hyΓ⟩ := Finset.mem_sdiff.mp hyi'
    have hi'C : i' ∉ C := (Finset.mem_sdiff.mp hi').2
    have hne : i ≠ i' := fun h => hi'C (h ▸ hi)
    have hadj : G.Adj i i' := (SimpleGraph.fromRel_adj _ _ _).mpr ⟨hne, Or.inl ⟨y, hyi, hyi', hyΓ⟩⟩
    exact hi'C (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((Finset.mem_filter.mp hi).2).trans hadj.reachable⟩)

end GaussianBlockSpin
