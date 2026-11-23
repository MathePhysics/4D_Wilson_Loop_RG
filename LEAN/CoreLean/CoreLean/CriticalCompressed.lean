/-
`thm:critical`(ii) of BALABAN_CORE.tex (`615c66b253fe`) at the level of the operators, with the inverses taken on
compressed spaces (`def:dirichlet-domain`(i), `def:operators`: the inverses on the forms which vanish outside the
Dirichlet domain and have their values in `𝔤^c`), extending `CriticalTheorem.critical_ii`, whose hypotheses ask for
inverses on the whole spaces.

The compressions are idempotent maps `Π` on `E` and `Π_F` on `F` which are symmetric for the pairings. The inverses enter
only through their compressed properties, which `CompressedInverse.cinv` has: `G_c` is supported by `Π` on both sides
and inverts `Π(Δ_𝖺 - Δ^{(2)})Π` from the left on the range of `Π`; `G` is supported by `Π` and inverts `ΠΔ_𝖺` from the
right; `(QG_cQ^*)^{-1}` inverts `QG_cQ^*` from the left on the range of `Π_F`; `(QGQ^*)^{-1}` is supported by `Π_F` and
inverts `Π_FQGQ^*` from the right. Two further inputs: `Q` maps the range of `Π` into that of `Π_F` (for the projection
onto `𝔤^c`: `Q` of a form with values in `𝔤^c` has values in `𝔤^c`, `prop:relative-average`, "The remainder and the site
factors", and its composites), and the weight `𝖺` preserves the range of `Π_F`. The preimage `A'` lies in the range of
`Π`, and the criticality is the vanishing on the variations `δ` in the range of `Π` with `Qδ = 0`.

Main results: `second_equation_c` (`A₀ = A' - H₀𝔟` is a fixed point of `Φ₀`), `critical_ii_c` (`A = 𝓗(𝖷(A))`). For
`Π = 1`, `Π_F = 1` the hypotheses are those of `critical_ii`.
-/
import CoreLean.CriticalTheorem

open LinearMap (BilinForm)

noncomputable section

namespace CoreLean
namespace CriticalCompressed

open CriticalTheorem

variable {K E F : Type*} [Field K] [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]

variable (Q : E →ₗ[K] F) (Qs : F →ₗ[K] E) (Δ Δ₂ DRD Gc G : E →ₗ[K] E) (a Minv M0inv : F →ₗ[K] F)
  (P : E →ₗ[K] E) (PF : F →ₗ[K] F)

/-- `G̃Q^*Π_F = 0`, from `(QG_cQ^*)^{-1}QG_cQ^*Π_F = Π_F`. -/
lemma Gt_Qs_c (hMinvL : ∀ y, Minv (Q (Gc (Qs (PF y)))) = PF y) (y : F) :
    Gt Q Qs Gc Minv (Qs (PF y)) = 0 := by
  simp only [Gt, LinearMap.sub_apply, LinearMap.comp_apply, hMinvL, sub_self]

/-- `G̃Π = G̃`. -/
lemma Gt_P (hGcP : ∀ x, Gc (P x) = Gc x) (x : E) : Gt Q Qs Gc Minv (P x) = Gt Q Qs Gc Minv x := by
  simp only [Gt, LinearMap.sub_apply, LinearMap.comp_apply, hGcP]

/-- `G̃(Δ_𝖺 - Δ^{(2)})x = x - H_cQx` for `x` in the range of `Π`. -/
lemma Gt_inv_c (hGcL : ∀ x, Gc ((Delta_a Q Qs Δ DRD a - Δ₂) (P x)) = P x) (x : E) (hx : P x = x) :
    Gt Q Qs Gc Minv ((Delta_a Q Qs Δ DRD a - Δ₂) x) = x - Hc Qs Gc Minv (Q x) := by
  have hy : Gc ((Delta_a Q Qs Δ DRD a - Δ₂) x) = x := by have := hGcL x; rwa [hx] at this
  generalize (Delta_a Q Qs Δ DRD a - Δ₂) x = y at hy ⊢
  simp only [Gt, Hc, LinearMap.sub_apply, LinearMap.comp_apply, hy]

/-- `H_c𝔟 = H₀𝔟 + G̃Δ^{(2)}H₀𝔟` for `𝔟` in the range of `Π_F`. -/
lemma Hc_eq_c (hGcL : ∀ x, Gc ((Delta_a Q Qs Δ DRD a - Δ₂) (P x)) = P x) (hGcP : ∀ x, Gc (P x) = Gc x)
    (hMinvL : ∀ y, Minv (Q (Gc (Qs (PF y)))) = PF y) (hGP : ∀ x, P (G x) = G x)
    (hGR : ∀ x, P (Delta_a Q Qs Δ DRD a (G x)) = P x) (hM0P : ∀ y, PF (M0inv y) = M0inv y)
    (hM0R : ∀ y, PF (Q (G (Qs (M0inv y)))) = PF y) (hQpres : ∀ x, PF (Q (P x)) = Q (P x)) (b : F)
    (hb : PF b = b) :
    Hc Qs Gc Minv b = H0 Qs G M0inv b + Gt Q Qs Gc Minv (Δ₂ (H0 Qs G M0inv b)) := by
  have hH : P (H0 Qs G M0inv b) = H0 Qs G M0inv b := hGP _
  have h1 := Gt_inv_c Q Qs Δ Δ₂ DRD Gc a Minv P hGcL (H0 Qs G M0inv b) hH
  have hGa : Gt Q Qs Gc Minv (Delta_a Q Qs Δ DRD a (H0 Qs G M0inv b)) = 0 := by
    rw [← Gt_P Q Qs Gc Minv P hGcP, H0, LinearMap.comp_apply, LinearMap.comp_apply, hGR,
      Gt_P Q Qs Gc Minv P hGcP, ← hM0P, Gt_Qs_c Q Qs Gc Minv PF hMinvL]
  have h3 : Q (H0 Qs G M0inv b) = b := by
    rw [← hH, ← hQpres, hH]
    simp only [H0, LinearMap.comp_apply]
    rw [hM0R, hb]
  rw [LinearMap.sub_apply, map_sub, hGa, zero_sub, h3] at h1
  calc Hc Qs Gc Minv b = H0 Qs G M0inv b - (H0 Qs G M0inv b - Hc Qs Gc Minv b) := by abel
    _ = H0 Qs G M0inv b + Gt Q Qs Gc Minv (Δ₂ (H0 Qs G M0inv b)) := by rw [← h1]; abel

/-- **The second equation, compressed**: if `Π(J + (Δ(U₀) - Δ^{(2)})A' + 𝖭(A')) = ΠQ^*Π_Fμ`, `RD^*A' = 0`, `QA' = 𝔟`
and `ΠA' = A'`, then `A₀ = A' - H₀𝔟` is a fixed point of `Φ₀` at `𝔄 = H₀𝔟`. -/
theorem second_equation_c (hPF : ∀ y, PF (PF y) = PF y)
    (hGcL : ∀ x, Gc ((Delta_a Q Qs Δ DRD a - Δ₂) (P x)) = P x) (hGcP : ∀ x, Gc (P x) = Gc x)
    (hMinvL : ∀ y, Minv (Q (Gc (Qs (PF y)))) = PF y) (hGP : ∀ x, P (G x) = G x)
    (hGR : ∀ x, P (Delta_a Q Qs Δ DRD a (G x)) = P x) (hM0P : ∀ y, PF (M0inv y) = M0inv y)
    (hM0R : ∀ y, PF (Q (G (Qs (M0inv y)))) = PF y) (hQpres : ∀ x, PF (Q (P x)) = Q (P x))
    (hapres : ∀ y, PF (a (PF y)) = a (PF y)) (N : E → E) (J A' : E) (b μ : F)
    (hf : P (J + (Δ - Δ₂) A' + N A') = P (Qs (PF μ))) (hD : DRD A' = 0) (hb : Q A' = b) (hA' : P A' = A') :
    A' - H0 Qs G M0inv b = Phi0 Q Qs Δ₂ Gc Minv N J (H0 Qs G M0inv b) (A' - H0 Qs G M0inv b) := by
  have hbF : PF b = b := by rw [← hb, ← hA', hQpres]
  set ν := PF μ + a b
  have hν : PF ν = ν := by
    simp only [ν, map_add, hPF]
    rw [← hbF, hapres]
  -- `Π(Δ_𝖺 - Δ^{(2)})A' = Π(Q^*ν - J - 𝖭(A'))`
  have e1 : (Delta_a Q Qs Δ DRD a - Δ₂) A' = (Δ - Δ₂) A' + Qs (a b) := by
    simp only [Delta_a, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, hD, hb]; abel
  have h1 : P ((Delta_a Q Qs Δ DRD a - Δ₂) A') = P (Qs ν - J - N A') := by
    rw [map_add, map_add] at hf
    rw [e1, map_add, show P ((Δ - Δ₂) A') = P (Qs (PF μ)) - P J - P (N A') by rw [← hf]; abel]
    simp only [ν, map_add, map_sub]; abel
  -- apply `G_c`
  have h2 : A' = Gc (Qs ν) - Gc (J + N A') := by
    calc A' = Gc ((Delta_a Q Qs Δ DRD a - Δ₂) (P A')) := by rw [hGcL, hA']
      _ = Gc (P ((Delta_a Q Qs Δ DRD a - Δ₂) A')) := by rw [hA', hGcP]
      _ = Gc (Qs ν - J - N A') := by rw [h1, hGcP]
      _ = Gc (Qs ν) - Gc (J + N A') := by rw [map_sub, map_sub, map_add Gc J (N A')]; abel
  -- apply `Q` and solve for `ν`
  have hq : Q (Gc (Qs ν)) = b + Q (Gc (J + N A')) := by
    have := congrArg Q h2
    rw [hb, map_sub] at this
    rw [this]; abel
  have h3 : ν = Minv (b + Q (Gc (J + N A'))) := by
    calc ν = PF ν := hν.symm
      _ = Minv (Q (Gc (Qs (PF ν)))) := (hMinvL ν).symm
      _ = Minv (b + Q (Gc (J + N A'))) := by rw [hν, hq]
  -- `A' = H_c𝔟 - G̃(J + 𝖭(A'))`
  have h4 : A' = Hc Qs Gc Minv b - Gt Q Qs Gc Minv (J + N A') := by
    calc A' = Gc (Qs ν) - Gc (J + N A') := h2
      _ = Gc (Qs (Minv (b + Q (Gc (J + N A'))))) - Gc (J + N A') := by rw [← h3]
      _ = Hc Qs Gc Minv b - Gt Q Qs Gc Minv (J + N A') := by
        simp only [Hc, Gt, LinearMap.comp_apply, LinearMap.sub_apply, map_add]
        abel
  rw [Hc_eq_c Q Qs Δ Δ₂ DRD Gc G a Minv M0inv P PF hGcL hGcP hMinvL hGP hGR hM0P hM0R hQpres b hbF] at h4
  unfold Phi0
  rw [sub_add_cancel]
  conv_lhs => rw [h4]
  rw [map_add]; abel

/-- **`thm:critical`(ii) with the inverses on compressed spaces**: `A = 𝓗(𝖷(A))`. -/
theorem critical_ii_c [FiniteDimensional K E] [FiniteDimensional K F] (BE : BilinForm K E) (BF : BilinForm K F)
    (hE : BE.Nondegenerate) (hF : BF.Nondegenerate) (hQ : ∀ μ A, BE (Qs μ) A = BF μ (Q A))
    (hP : ∀ x, P (P x) = P x) (hPs : ∀ x y, BE (P x) y = BE x (P y))
    (hPF : ∀ y, PF (PF y) = PF y) (hPFs : ∀ u v, BF (PF u) v = BF u (PF v))
    (hGcL : ∀ x, Gc ((Delta_a Q Qs Δ DRD a - Δ₂) (P x)) = P x) (hGcP : ∀ x, Gc (P x) = Gc x)
    (hMinvL : ∀ y, Minv (Q (Gc (Qs (PF y)))) = PF y) (hGP : ∀ x, P (G x) = G x)
    (hGR : ∀ x, P (Delta_a Q Qs Δ DRD a (G x)) = P x) (hM0P : ∀ y, PF (M0inv y) = M0inv y)
    (hM0R : ∀ y, PF (Q (G (Qs (M0inv y)))) = PF y)
    -- `prop:relative-average`: `Q` maps the compressed forms into the compressed functions
    (hQpres : ∀ x, PF (Q (P x)) = Q (P x)) (hapres : ∀ y, PF (a (PF y)) = a (PF y))
    (N : E → E) (J : E) (T : E → E) (X : E → F) (A0fix : E → E) (ball : E → Set E)
    -- `prop:fixed-points`: uniqueness of the fixed point of `Φ₀` on its ball
    (huniq : ∀ 𝔄, ∀ A₀ ∈ ball 𝔄, Phi0 Q Qs Δ₂ Gc Minv N J 𝔄 A₀ = A₀ → A₀ = A0fix 𝔄)
    (A A' : E)
    -- `prop:linearising`(ii), `lem:real-preimage`; the preimage is a compressed form
    (hT : T A' = A) (hD : DRD A' = 0) (hX : Q A' = X A) (hA' : P A' = A')
    -- criticality through `lem:critical`(iii) and `eq:functional`, on the compressed variations
    (hcrit : ∀ δ, P δ = δ → Q δ = 0 → BE (J + (Δ - Δ₂) A' + N A') δ = 0)
    -- the step "Uniqueness": `A' - H₀𝔟` lies in the ball
    (hball : A' - H0 Qs G M0inv (X A) ∈ ball (H0 Qs G M0inv (X A))) :
    A = T (A0fix (H0 Qs G M0inv (X A)) + H0 Qs G M0inv (X A)) := by
  -- the compressed `Q` and its transpose
  have hQc : ∀ μ A, BE ((P ∘ₗ Qs ∘ₗ PF) μ) A = BF μ ((PF ∘ₗ Q ∘ₗ P) A) := fun μ A => by
    simp only [LinearMap.comp_apply]
    rw [hPs, hQ, hPFs]
  have hfc : ∀ δ, (PF ∘ₗ Q ∘ₗ P) δ = 0 → BE (P (J + (Δ - Δ₂) A' + N A')) δ = 0 := fun δ hδ => by
    simp only [LinearMap.comp_apply, hQpres] at hδ
    rw [hPs]
    exact hcrit (P δ) (hP δ) hδ
  obtain ⟨μ, hμ⟩ := mem_range_transpose BE BF hE hF (PF ∘ₗ Q ∘ₗ P) (P ∘ₗ Qs ∘ₗ PF) hQc _ hfc
  have hμ' : P (J + (Δ - Δ₂) A' + N A') = P (Qs (PF μ)) := by rw [hμ]; rfl
  have hfix := second_equation_c Q Qs Δ Δ₂ DRD Gc G a Minv M0inv P PF hPF hGcL hGcP hMinvL hGP hGR hM0P hM0R
    hQpres hapres N J A' (X A) μ hμ' hD hX hA'
  have h := huniq _ _ hball hfix.symm
  rw [← h, sub_add_cancel, hT]

/-- **`G̃J = 0` at a critical `U₀`, compressed** (`thm:critical`(iii)): `⟨G̃J, y⟩ = ⟨J, G̃y⟩` by the symmetries of `G_c`
and of `(QG_cQ^*)^{-1}`, and `G̃y` is a compressed form with `QG̃y = 0`, which `J` annihilates. -/
theorem Gtilde_J_c [FiniteDimensional K E] (BE : BilinForm K E) (BF : BilinForm K F) (hE : BE.Nondegenerate)
    (hEs : ∀ x y, BE x y = BE y x) (hFs : ∀ u v, BF u v = BF v u) (hQ : ∀ μ A, BE (Qs μ) A = BF μ (Q A))
    (hGcP : ∀ x, P (Gc x) = Gc x) (hGcs : ∀ x y, BE (Gc x) y = BE x (Gc y))
    (hMinvs : ∀ u v, BF (Minv u) v = BF u (Minv v))
    (hQGt : ∀ x, PF (Q (Gt Q Qs Gc Minv x)) = 0) (hQpres : ∀ x, PF (Q (P x)) = Q (P x))
    (J : E) (hJ : ∀ δ, P δ = δ → Q δ = 0 → BE J δ = 0) : Gt Q Qs Gc Minv J = 0 := by
  have hGtP : ∀ x, P (Gt Q Qs Gc Minv x) = Gt Q Qs Gc Minv x := fun x => by
    simp only [Gt, LinearMap.sub_apply, LinearMap.comp_apply, map_sub, hGcP]
  have hpair : ∀ y, BE (Gt Q Qs Gc Minv J) y = BE J (Gt Q Qs Gc Minv y) := fun y => by
    have e : BE (Gc (Qs (Minv (Q (Gc J))))) y = BE J (Gc (Qs (Minv (Q (Gc y))))) := by
      calc BE (Gc (Qs (Minv (Q (Gc J))))) y = BE (Qs (Minv (Q (Gc J)))) (Gc y) := hGcs _ _
        _ = BF (Minv (Q (Gc J))) (Q (Gc y)) := hQ _ _
        _ = BF (Q (Gc J)) (Minv (Q (Gc y))) := hMinvs _ _
        _ = BF (Minv (Q (Gc y))) (Q (Gc J)) := hFs _ _
        _ = BE (Qs (Minv (Q (Gc y)))) (Gc J) := (hQ _ _).symm
        _ = BE (Gc (Qs (Minv (Q (Gc y))))) J := (hGcs _ _).symm
        _ = BE J (Gc (Qs (Minv (Q (Gc y))))) := hEs _ _
    show BE (Gc J - Gc (Qs (Minv (Q (Gc J))))) y = BE J (Gc y - Gc (Qs (Minv (Q (Gc y)))))
    rw [map_sub, LinearMap.sub_apply, map_sub, e, hGcs]
  apply hE.1
  intro y
  rw [hpair]
  apply hJ _ (hGtP y)
  rw [← hGtP y, ← hQpres, hGtP y, hQGt]

end CriticalCompressed
end CoreLean

end
