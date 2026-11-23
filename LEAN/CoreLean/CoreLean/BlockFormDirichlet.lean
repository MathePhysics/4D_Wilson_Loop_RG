/-
`cor:block-form-dirichlet` of BALABAN_CORE.tex (`a021c13be348`), the operator part of its proof in abstract form. With
`G'` symmetric (on the `0`-forms vanishing outside `Ω_D`, `thm:propagators`(i)), `Q'^*` the transpose of `Q'`, and
`(Q'G'^2Q'^*)⁻¹` a symmetric two-sided inverse, `P = G'Q'^*(Q'G'^2Q'^*)⁻¹Q'G'` is symmetric with `P² = P`
(`proj_idem`, `proj_symm`), so that `R = I - P` is an orthogonal projection and
`0 ≤ ⟨v, Rv⟩ ≤ ‖v‖²` (`proj_bounds`): the second term `⟨D^*_Uf, RD^*_Uf⟩` of `⟨f, Δ_𝖺f⟩` is at most `‖D^*_Uf‖²_2`, as on
the torus. With the other two terms bounded as on the torus, `⟨f, Δ_𝖺f⟩ ≤ C_⋆𝗆`, and `eq:block-form-lower` follows from
`block_form_lower` with the same `γ_b` (`block_form_dirichlet`).
-/
import CoreLean.BlockForm

open scoped InnerProductSpace

noncomputable section

namespace CoreLean
namespace BlockFormDirichlet

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [NormedAddCommGroup K]
  [InnerProductSpace ℝ K]

/-- The projection `P = G'Q'^*(Q'G'^2Q'^*)⁻¹Q'G'`. -/
def proj (G : H →L[ℝ] H) (Q : H →L[ℝ] K) (Qs : K →L[ℝ] H) (Minv : K →L[ℝ] K) : H →L[ℝ] H :=
  G.comp (Qs.comp (Minv.comp (Q.comp G)))

variable (G : H →L[ℝ] H) (Q : H →L[ℝ] K) (Qs : K →L[ℝ] H) (Minv : K →L[ℝ] K)

/-- `P² = P`. -/
theorem proj_idem (hM : ∀ k, Minv (Q (G (G (Qs k)))) = k) (v : H) :
    proj G Q Qs Minv (proj G Q Qs Minv v) = proj G Q Qs Minv v := by
  simp only [proj, ContinuousLinearMap.comp_apply, hM]

/-- `P` is symmetric. -/
theorem proj_symm (hG : ∀ u v, ⟪G u, v⟫_ℝ = ⟪u, G v⟫_ℝ) (hQ : ∀ u k, ⟪Q u, k⟫_ℝ = ⟪u, Qs k⟫_ℝ)
    (hMs : ∀ k k', ⟪Minv k, k'⟫_ℝ = ⟪k, Minv k'⟫_ℝ) (u v : H) :
    ⟪proj G Q Qs Minv u, v⟫_ℝ = ⟪u, proj G Q Qs Minv v⟫_ℝ := by
  simp only [proj, ContinuousLinearMap.comp_apply]
  calc ⟪G (Qs (Minv (Q (G u)))), v⟫_ℝ = ⟪Qs (Minv (Q (G u))), G v⟫_ℝ := hG _ _
    _ = ⟪G v, Qs (Minv (Q (G u)))⟫_ℝ := by rw [real_inner_comm]
    _ = ⟪Q (G v), Minv (Q (G u))⟫_ℝ := (hQ _ _).symm
    _ = ⟪Minv (Q (G v)), Q (G u)⟫_ℝ := (hMs _ _).symm
    _ = ⟪Q (G u), Minv (Q (G v))⟫_ℝ := by rw [real_inner_comm]
    _ = ⟪G u, Qs (Minv (Q (G v)))⟫_ℝ := hQ _ _
    _ = ⟪u, G (Qs (Minv (Q (G v))))⟫_ℝ := hG _ _

/-- **`R = I - P` is an orthogonal projection**: `0 ≤ ⟨v, v - Pv⟩ ≤ ‖v‖²`. -/
theorem proj_bounds (hM : ∀ k, Minv (Q (G (G (Qs k)))) = k) (hG : ∀ u v, ⟪G u, v⟫_ℝ = ⟪u, G v⟫_ℝ)
    (hQ : ∀ u k, ⟪Q u, k⟫_ℝ = ⟪u, Qs k⟫_ℝ) (hMs : ∀ k k', ⟪Minv k, k'⟫_ℝ = ⟪k, Minv k'⟫_ℝ) (v : H) :
    0 ≤ ⟪v, v - proj G Q Qs Minv v⟫_ℝ ∧ ⟪v, v - proj G Q Qs Minv v⟫_ℝ ≤ ‖v‖ ^ 2 := by
  have hidem := proj_idem G Q Qs Minv hM
  have hsym := proj_symm G Q Qs Minv hG hQ hMs
  set P := proj G Q Qs Minv
  -- `⟨v, Pv⟩ = ‖Pv‖²`
  have h1 : ⟪v, P v⟫_ℝ = ⟪P v, P v⟫_ℝ := by rw [hsym, hidem]
  -- `⟨v, v - Pv⟩ = ‖v - Pv‖²`
  have h2 : ⟪v, v - P v⟫_ℝ = ⟪v - P v, v - P v⟫_ℝ := by
    have : ⟪P v, v⟫_ℝ = ⟪P v, P v⟫_ℝ := by rw [real_inner_comm, h1]
    simp only [inner_sub_left, inner_sub_right, this, h1]
    ring
  constructor
  · rw [h2]; exact real_inner_self_nonneg
  · rw [inner_sub_right, h1, real_inner_self_eq_norm_sq]
    have := real_inner_self_nonneg (x := P v)
    linarith

/-- **`cor:block-form-dirichlet`**: the energy bound on the Dirichlet domain and `eq:block-form-lower`. -/
theorem block_form_dirichlet (Δ Gd : H →L[ℝ] H) (hΔG : ∀ y, Δ (Gd y) = y)
    (hsymΔ : ∀ u v, ⟪u, Δ v⟫_ℝ = ⟪Δ u, v⟫_ℝ) (hpos : ∀ u, 0 ≤ ⟪u, Δ u⟫_ℝ)
    (hM : ∀ k, Minv (Q (G (G (Qs k)))) = k) (hG : ∀ u v, ⟪G u, v⟫_ℝ = ⟪u, G v⟫_ℝ)
    (hQ : ∀ u k, ⟪Q u, k⟫_ℝ = ⟪u, Qs k⟫_ℝ) (hMs : ∀ k k', ⟪Minv k, k'⟫_ℝ = ⟪k, Minv k'⟫_ℝ)
    (x f w : H) {m C T1 T3 : ℝ} (hC : 0 < C) (hxf : m / 2 ≤ ⟪x, f⟫_ℝ)
    (hdecomp : ⟪f, Δ f⟫_ℝ = T1 + ⟪w, w - proj G Q Qs Minv w⟫_ℝ + T3) (htorus : T1 + ‖w‖ ^ 2 + T3 ≤ C * m) :
    m / (4 * C) ≤ ⟪x, Gd x⟫_ℝ := by
  have hb := (proj_bounds G Q Qs Minv hM hG hQ hMs w).2
  exact BlockForm.block_form_lower Δ Gd hΔG hsymΔ hpos x f hC hxf (by linarith)

end BlockFormDirichlet
end CoreLean

end
