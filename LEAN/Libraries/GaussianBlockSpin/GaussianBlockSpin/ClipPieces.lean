import GaussianBlockSpin.MonomialPolynomials
import GaussianBlockSpin.DecouplingIterate

/-! Monomials as bounded local pieces: on the cut-off coordinates `|ξ_c| ≤ β` a monomial equals its clipped version
`b_X ∏_l clip_β(ξ_{X_l})` (clipPieces_sum_eq), which is bounded by `|b_X| β^p` everywhere (clipPieces). -/

namespace GaussianBlockSpin

open MeasureTheory ProbabilityTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

/-- `clip_β(x) = max(-β, min(β, x))`. -/
def clipβ (β x : ℝ) : ℝ := max (-β) (min β x)

lemma abs_clipβ_le {β : ℝ} (hβ : 0 ≤ β) (x : ℝ) : |clipβ β x| ≤ β := by
  unfold clipβ
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

lemma clipβ_of_mem {β x : ℝ} (hx : x ∈ Set.Icc (-β) β) : clipβ β x = x := by
  unfold clipβ
  rw [min_eq_right hx.2, max_eq_right hx.1]

lemma continuous_clipβ (β : ℝ) : Continuous (clipβ β) := by
  unfold clipβ; fun_prop

/-- The clipped monomial `b_X ∏_l clip_β(ξ_{X_l})`. -/
def clipPiece (β : ℝ) (b : MonoIdx ι D → ℝ) (X : MonoIdx ι D) (ξ : ι → ℝ) : ℝ :=
  b X * ∏ l, clipβ β (ξ (X.2 l))

/-- **The clipped monomials of a set `S` as local pieces**, indexed by `S`. -/
def clipPieces {β : ℝ} (hβ : 0 ≤ β) (b : MonoIdx ι D → ℝ) (S : Finset (MonoIdx ι D)) : LocalPieces ι S where
  supp X := monoSupp X.1
  h X := clipPiece β b X.1
  a X := |b X.1| * β ^ (X.1.1 : ℕ)
  loc X := by
    intro ξ ξ' h
    unfold clipPiece
    congr 1
    exact Finset.prod_congr rfl fun l _ => by rw [h _ (by simp [monoSupp])]
  meas X := by
    unfold clipPiece
    exact ((Finset.measurable_prod _ fun l _ =>
      (continuous_clipβ β).measurable.comp (measurable_pi_apply (X.1.2 l)))).const_mul _
  bdd X ξ := by
    unfold clipPiece
    rw [abs_mul, Finset.abs_prod]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    calc ∏ l, |clipβ β (ξ (X.1.2 l))| ≤ ∏ _l : Fin X.1.1, β :=
          Finset.prod_le_prod₀ (fun l _ => abs_nonneg _) fun l _ => abs_clipβ_le hβ _
      _ = β ^ (X.1.1 : ℕ) := by simp

omit [Fintype ι] in
/-- On the cut-off coordinates the clipped pieces sum to the polynomial. -/
lemma clipPieces_sum_eq {β : ℝ} (hβ : 0 ≤ β) (b : MonoIdx ι D → ℝ) (S : Finset (MonoIdx ι D)) {ξ : ι → ℝ}
    (hξ : ∀ c, ξ c ∈ Set.Icc (-β) β) :
    (clipPieces hβ b S).sum Finset.univ ξ = ∑ X ∈ S, monoPiece b X ξ := by
  unfold LocalPieces.sum
  rw [← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun X _ => ?_
  show clipPiece β b X.1 ξ = monoPiece b X.1 ξ
  unfold clipPiece monoPiece monoVal
  congr 1
  exact Finset.prod_congr rfl fun l _ => clipβ_of_mem (hξ _)

end GaussianBlockSpin
