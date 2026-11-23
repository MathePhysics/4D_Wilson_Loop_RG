import GaussianBlockSpin.CumulantTaylor

/-! Local functions of independent coordinates (the product measure of the cumulant expansion of [2], Bałaban I
L1409-L1417, after writing the Gaussian field through independent variables): under a product probability measure
`Measure.pi μ` on `κ → ℝ`, functions that depend on disjoint sets of coordinates are independent, so
* integral_mul_of_disjoint: `∫ G H = ∫ G ∫ H` if `G` depends on `P`, `H` on `R`, `P ∩ R = ∅`;
* jointCumulant_local_eq_zero: the joint cumulant of a family of local functions vanishes on every index set that
  splits into two nonempty parts with disjoint coordinate sets ("disconnected"). -/

namespace GaussianBlockSpin

open MeasureTheory ProbabilityTheory

variable {κ : Type*} [Fintype κ] [DecidableEq κ] (μ : κ → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]

/-- The extension by `0` of a configuration on `P`. -/
def extendZero (P : Finset κ) (y : P → ℝ) : κ → ℝ := fun i => if h : i ∈ P then y ⟨i, h⟩ else 0

omit [Fintype κ] in
lemma measurable_extendZero (P : Finset κ) : Measurable (extendZero P) := by
  refine measurable_pi_iff.mpr fun i => ?_
  by_cases h : i ∈ P
  · simp only [extendZero, h, ↓reduceDIte]; exact measurable_pi_apply _
  · simp only [extendZero, h, ↓reduceDIte]; exact measurable_const

omit [Fintype κ] in
/-- A function depending only on the coordinates in `P` factors through the restriction to `P`. -/
lemma dependsOn_eq_comp {G : (κ → ℝ) → ℝ} {P : Finset κ} (hG : DependsOn G (P : Set κ)) (ω : κ → ℝ) :
    G ω = G (extendZero P (fun i : P => ω i)) := by
  refine hG fun i hi => ?_
  simp [extendZero, Finset.mem_coe.mp hi]

/-- **Functions of disjoint coordinate sets are independent**: `∫ G H = ∫ G ∫ H` under a product probability measure if
`G` depends only on the coordinates in `P`, `H` only on those in `R`, and `P ∩ R = ∅`. -/
theorem integral_mul_of_disjoint {G H : (κ → ℝ) → ℝ} {P R : Finset κ} (hPR : Disjoint P R)
    (hG : DependsOn G (P : Set κ)) (hH : DependsOn H (R : Set κ)) (mG : Measurable G) (mH : Measurable H) :
    ∫ ω, G ω * H ω ∂(Measure.pi μ) = (∫ ω, G ω ∂(Measure.pi μ)) * ∫ ω, H ω ∂(Measure.pi μ) := by
  have hind : iIndepFun (fun i (ω : κ → ℝ) => ω i) (Measure.pi μ) :=
    iIndepFun_pi (X := fun _ (x : ℝ) => x) (fun _ => measurable_id.aemeasurable)
  have hPRind := hind.indepFun_finset P R hPR (fun i => measurable_pi_apply i)
  have hcomp := hPRind.comp (mG.comp (measurable_extendZero P)) (mH.comp (measurable_extendZero R))
  have hGe : G = fun ω => G (extendZero P (fun i : P => ω i)) := funext (dependsOn_eq_comp hG)
  have hHe : H = fun ω => H (extendZero R (fun i : R => ω i)) := funext (dependsOn_eq_comp hH)
  have hrP : Measurable (fun (ω : κ → ℝ) (i : P) => ω i) := measurable_pi_iff.mpr fun i => measurable_pi_apply _
  have hrR : Measurable (fun (ω : κ → ℝ) (i : R) => ω i) := measurable_pi_iff.mpr fun i => measurable_pi_apply _
  have := hcomp.integral_mul_eq_mul_integral
    ((mG.comp (measurable_extendZero P)).comp hrP).aestronglyMeasurable
    ((mH.comp (measurable_extendZero R)).comp hrR).aestronglyMeasurable
  conv_lhs => rw [hGe, hHe]
  conv_rhs => rw [hGe, hHe]
  exact this

omit [Fintype κ] in
/-- A product of functions each depending on its own coordinate set depends on the union. -/
lemma dependsOn_prod {k : ℕ} {Y : Fin k → (κ → ℝ) → ℝ} {P : Fin k → Finset κ}
    (hY : ∀ i, DependsOn (Y i) (P i : Set κ)) (U : Finset (Fin k)) :
    DependsOn (fun ω => ∏ i ∈ U, Y i ω) ((U.biUnion P : Finset κ) : Set κ) := by
  intro ω ω' h
  refine Finset.prod_congr rfl fun i hi => hY i fun j hj => h j ?_
  exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_coe.mp hj⟩)

/-- **Joint cumulants of disconnected families of local functions vanish**: if `S` splits into nonempty `A` and
`S \ A` whose coordinate sets are disjoint, the joint cumulant (over `S`) of the moments
`T ↦ ∫ ∏_{i ∈ T} Y_i` under a product probability measure is `0`. -/
theorem jointCumulant_local_eq_zero {k : ℕ} (Y : Fin k → (κ → ℝ) → ℝ) (P : Fin k → Finset κ)
    (hY : ∀ i, DependsOn (Y i) (P i : Set κ)) (mY : ∀ i, Measurable (Y i)) {S A : Finset (Fin k)} (hAS : A ⊆ S)
    (hA : A.Nonempty) (hSA : (S \ A).Nonempty) (hdisj : Disjoint (A.biUnion P) ((S \ A).biUnion P)) :
    jointCumulant (fun T => ∫ ω, ∏ i ∈ T, Y i ω ∂(Measure.pi μ)) S = 0 := by
  refine jointCumulant_eq_zero_of_split _ (by simp) hAS hA hSA fun U hU => ?_
  have hsplit : ∀ ω, ∏ i ∈ U, Y i ω = (∏ i ∈ U ∩ A, Y i ω) * ∏ i ∈ U \ A, Y i ω := fun ω =>
    (Finset.prod_inter_mul_prod_sdiff U A _).symm
  simp_rw [hsplit]
  refine integral_mul_of_disjoint μ (P := (U ∩ A).biUnion P) (R := (U \ A).biUnion P) ?_ (dependsOn_prod hY _)
    (dependsOn_prod hY _) (Finset.measurable_prod _ fun i _ => mY i) (Finset.measurable_prod _ fun i _ => mY i)
  refine Finset.disjoint_of_subset_left (Finset.biUnion_subset_biUnion_of_subset_left _ Finset.inter_subset_right) ?_
  refine Finset.disjoint_of_subset_right (Finset.biUnion_subset_biUnion_of_subset_left _ ?_) hdisj
  intro i hi
  obtain ⟨hiU, hiA⟩ := Finset.mem_sdiff.mp hi
  exact Finset.mem_sdiff.mpr ⟨hU hiU, hiA⟩

end GaussianBlockSpin
