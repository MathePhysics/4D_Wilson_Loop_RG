/-
`prop:sf-vector-lower` of BALABAN_CORE.tex (`c1d6d533fce5`), the quadratic forms and two steps which do not need the
comparison sequences, on the fine lattice (`a₀ = 1`) at the trivial configuration, the torus as the Dirichlet domain.

* `Ds1L_triv`: `∂^*A(x) = Σ_μ(A_μ(x - e_μ) - A_μ(x))`; `ds_le_grad`: `N‖∂^*A‖² ≤ 4‖∇A‖²` (in the norm of `V`).
* `formF`, `formA`: the forms `⟨A^*, Δ^F_𝖺A⟩ = ‖∇A‖² + Σ_ca_c²|(QA)(c)|²` (eq:sf-feynman-form) and
  `⟨A^*, Δ_𝖺(id)A⟩ = ⟨A^*, Δ^F_𝖺A⟩ - ‖P∂^*A‖²` (eq:sf-feynman, with `⟨g, Pg⟩ = ‖Pg‖²` at the trivial configuration),
  in the norm of `V`; `formA_le`: `formA ≤ formF`.
* `Pop_contr`: `‖Pg‖ ≤ ‖g‖`; `variational`: eq:sf-variational as `‖Pg‖² ≤ ‖g - Δλ‖²` for `λ ∈ N(Q')`.
* `ims`: the formula of Ismagilov, Morgan, and Simon for a form with a kernel: if `Σ_□h_□² = 1`, then
  `Σ_□q(h_□A) = q(A) - ½Re Σ_{x,x'}Σ_□(h_□(x) - h_□(x'))²⟨A(x), K(x, x')A(x')⟩`.
-/
import CoreLean.SFTwoLayersBounds

open Finset Matrix

noncomputable section

namespace CoreLean
namespace SFBounds

open Lattices SeqDom Blocks SmallFieldBlocks SFLocal SmallFieldDecay SmallFieldCoercivity
  SequenceOperators CompressedInverse ConcretePairing SFBox SFBox.SeqDomBox

variable (S : SeqDom) {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "NF" => SequenceAverages.N0 S

/-- `∂^*A(x) = Σ_μ(A_μ(x - e_μ) - A_μ(x))` at the trivial configuration. -/
lemma Ds1L_triv (A : Fin 4 → Site NF → Mat) (x : Site NF) :
    Ds1L a1 (cfgX (X0 S)) A x = ∑ μ, (A μ (x - unit NF μ) - A μ x) := by
  ext a b
  rw [Ds1L_entry, Matrix.sum_apply]
  simp only [dsF, Matrix.sub_apply]

lemma norm_sum4_sq {E : Type*} [NormedAddCommGroup E] (v : Fin 4 → E) : ‖∑ μ, v μ‖ ^ 2 ≤ 4 * ∑ μ, ‖v μ‖ ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin 4))) (f := fun μ => ‖v μ‖)
  simp only [card_univ, Fintype.card_fin] at h
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans (by exact_mod_cast h)

/-- **`N‖∂^*A‖² ≤ 4‖∇A‖²`.** -/
theorem ds_le_grad (A : Fin 4 → Site NF → Mat) :
    (N : ℝ) * ∑ x, hs2 (Ds1L a1 (cfgX (X0 S)) A x) ≤ 4 * gradNorm S A := by
  have e1 : ∀ x, (N : ℝ) * hs2 (Ds1L a1 (cfgX (X0 S)) A x) =
      ‖∑ μ, (emb (N := N) (A μ (x - unit NF μ)) - emb (A μ x))‖ ^ 2 := fun x => by
    rw [← norm_emb_sq, Ds1L_triv]
    congr 2
  rw [mul_sum]
  simp only [e1]
  have h2 : ∀ μ, ∑ x, ‖emb (N := N) (A μ (x - unit NF μ)) - emb (A μ x)‖ ^ 2 = ∑ x, gbond S A μ x μ := by
    intro μ
    exact Fintype.sum_equiv (Equiv.subRight (unit NF μ)) _ _ (fun x => by
      simp only [gbond, Equiv.subRight_apply, sub_add_cancel]; rw [norm_sub_rev])
  calc ∑ x, ‖∑ μ, (emb (N := N) (A μ (x - unit NF μ)) - emb (A μ x))‖ ^ 2
      ≤ ∑ x, 4 * ∑ μ, ‖emb (N := N) (A μ (x - unit NF μ)) - emb (A μ x)‖ ^ 2 :=
        sum_le_sum fun x _ => norm_sum4_sq _
    _ = 4 * ∑ μ, ∑ x, gbond S A μ x μ := by rw [← mul_sum, sum_comm]; simp only [h2]
    _ ≤ 4 * gradNorm S A := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        unfold gradNorm
        refine sum_le_sum fun μ _ => sum_le_sum fun x _ => ?_
        exact single_le_sum (f := fun ν => gbond S A μ x ν) (fun ν _ => by unfold gbond; positivity) (mem_univ μ)

/-- **`⟨A^*, Δ^F_𝖺A⟩`** (eq:sf-feynman-form, in the norm of `V`). -/
def formF (A : Fin 4 → Site NF → Mat) : ℝ := gradNorm S A + Qnorm S A

/-- **`⟨A^*, Δ_𝖺(id)A⟩ = ⟨A^*, Δ^F_𝖺A⟩ - ⟨(∂^*A)^*, P∂^*A⟩`** (eq:sf-feynman, the torus as the Dirichlet domain, in the
norm of `V`). -/
def formA [NeZero N] (A : Fin 4 → Site NF → Mat) : ℝ :=
  formF S A - N * ∑ x, hs2 (Pop S (X0 S) (W1 S) Set.univ (Ds1L a1 (cfgX (X0 S)) A) x)

/-- **`‖Pg‖ ≤ ‖g‖`** at the trivial configuration. -/
theorem Pop_contr [NeZero N] (ΩD : Set (Site NF)) (g : Site NF → Mat) :
    ∑ x, hs2 (Pop S (X0 S) (W1 S) ΩD g x) ≤ ∑ x, hs2 (g x) := by
  have hb := hb_triv (N := N) (S := S) ΩD
  have h := proj_le_of_ker S LinearMap.id (Pop S (X0 S) (W1 S) ΩD) (fun f => rfl) (Pop_idem S _ _ ΩD hb)
    (fun f g => (Pop_herm_triv S ΩD hb f g)) (Pop_norm_triv S ΩD hb) (fun g hg => by
      simp only [LinearMap.id_apply] at hg; rw [hg, map_zero]) g
  simpa using h

lemma formA_le [NeZero N] (A : Fin 4 → Site NF → Mat) : formA S A ≤ formF S A := by
  unfold formA
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have : 0 ≤ ∑ x, hs2 (Pop S (X0 S) (W1 S) Set.univ (Ds1L a1 (cfgX (X0 S)) A) x) :=
    sum_nonneg fun x _ => hs2_nonneg _
  nlinarith

/-- **eq:sf-variational** (the torus as the Dirichlet domain), the inequality: `‖Pg‖² ≤ ‖g - Δλ‖²` for `λ ∈ N(Q')`. -/
theorem variational [NeZero N] (g : Site NF → Mat) {lam : Site NF → Mat}
    (hlam : ∀ y ∈ detB S.toDomSeq, avgW S.toDomSeq (W1 S) y lam = 0) :
    ∑ x, hs2 (Pop S (X0 S) (W1 S) Set.univ g x) ≤
      ∑ x, hs2 ((g - Ds1L a1 (cfgX (X0 S)) (D0L a1 (cfgX (X0 S)) lam)) x) := by
  have e : Pop S (X0 S) (W1 S) Set.univ g =
      Pop S (X0 S) (W1 S) Set.univ (g - Ds1L a1 (cfgX (X0 S)) (D0L a1 (cfgX (X0 S)) lam)) := by
    rw [map_sub, Pop_DsD_null S hlam, sub_zero]
  rw [e]
  exact Pop_contr S Set.univ _

/-! ### `‖∇A‖² = ‖∂A‖² + ‖∂^*A‖²` on the torus -/

lemma sum_shift_site {β : Type*} [AddCommMonoid β] (F : Site NF → β) (c : Site NF) : ∑ x, F (x + c) = ∑ x, F x :=
  Fintype.sum_equiv (Equiv.addRight c) _ _ fun _ => rfl

/-- The summation by parts behind eq:sf-feynman: `Σ_x⟨∂_μa_ν, ∂_νa_μ⟩ = Σ_x⟨∂^*_νa_ν, ∂^*_μa_μ⟩`. -/
lemma sum_inner_swap {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (a : Fin 4 → Site NF → V)
    (μ ν : Fin 4) :
    ∑ x, inner ℂ (a ν (x + unit NF μ) - a ν x) (a μ (x + unit NF ν) - a μ x) =
      ∑ x, inner ℂ (a ν (x - unit NF ν) - a ν x) (a μ (x - unit NF μ) - a μ x) := by
  simp only [inner_sub_left, inner_sub_right, sum_sub_distrib, sum_add_distrib]
  have t1 : ∑ x, inner ℂ (a ν (x + unit NF μ)) (a μ (x + unit NF ν)) =
      ∑ x, inner ℂ (a ν (x - unit NF ν)) (a μ (x - unit NF μ)) := by
    rw [← sum_shift_site S (fun x => inner ℂ (a ν (x - unit NF ν)) (a μ (x - unit NF μ))) (unit NF μ + unit NF ν)]
    refine sum_congr rfl fun x _ => ?_
    congr 2 <;> abel
  have t2 : ∑ x, inner ℂ (a ν (x + unit NF μ)) (a μ x) = ∑ x, inner ℂ (a ν x) (a μ (x - unit NF μ)) := by
    rw [← sum_shift_site S (fun x => inner ℂ (a ν x) (a μ (x - unit NF μ))) (unit NF μ)]
    refine sum_congr rfl fun x _ => ?_
    simp only [add_sub_cancel_right]
  have t3 : ∑ x, inner ℂ (a ν x) (a μ (x + unit NF ν)) = ∑ x, inner ℂ (a ν (x - unit NF ν)) (a μ x) := by
    rw [← sum_shift_site S (fun x => inner ℂ (a ν (x - unit NF ν)) (a μ x)) (unit NF ν)]
    refine sum_congr rfl fun x _ => ?_
    simp only [add_sub_cancel_right]
  rw [t1, t2, t3]
  ring

/-- **`‖∇A‖² = ‖∂A‖² + ‖∂^*A‖²`** on the torus (in the norm of `V`). -/
theorem grad_identity (A : Fin 4 → Site NF → Mat) :
    gradNorm S A = N * curlE S A + N * ∑ x, hs2 (Ds1L a1 (cfgX (X0 S)) A x) := by
  set a : Fin 4 → Site NF → VS N 1 := fun μ x => emb (A μ x)
  set d : Fin 4 → Fin 4 → Site NF → VS N 1 := fun μ ν x => a ν (x + unit NF μ) - a ν x
  set s : Fin 4 → Site NF → VS N 1 := fun μ x => a μ (x - unit NF μ) - a μ x
  -- the three forms in `V`
  have hg : gradNorm S A = ∑ x, ∑ μ, ∑ ν, ‖d μ ν x‖ ^ 2 := by
    unfold gradNorm gbond
    rw [sum_comm]
    refine sum_congr rfl fun x _ => ?_
    rw [sum_comm]
  have hc : (N : ℝ) * curlE S A = ∑ x, 1 / 2 * ∑ μ, ∑ ν, ‖d μ ν x - d ν μ x‖ ^ 2 := by
    unfold curlE
    rw [mul_sum]
    refine sum_congr rfl fun x _ => ?_
    rw [mul_left_comm, mul_sum]
    congr 1
    refine sum_congr rfl fun μ _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun ν _ => ?_
    rw [← norm_emb_sq]
    congr 2
  have hs : (N : ℝ) * ∑ x, hs2 (Ds1L a1 (cfgX (X0 S)) A x) = ∑ x, ‖∑ μ, s μ x‖ ^ 2 := by
    rw [mul_sum]
    refine sum_congr rfl fun x _ => ?_
    rw [← norm_emb_sq, Ds1L_triv]
    congr 2
  rw [hg, hc, hs]
  -- the expansions
  have e1 : ∀ x, 1 / 2 * ∑ μ, ∑ ν, ‖d μ ν x - d ν μ x‖ ^ 2 =
      ∑ μ, ∑ ν, ‖d μ ν x‖ ^ 2 - ∑ μ, ∑ ν, (inner ℂ (d μ ν x) (d ν μ x)).re := fun x => by
    have h1 : ∀ μ ν, ‖d μ ν x - d ν μ x‖ ^ 2 = ‖d μ ν x‖ ^ 2 - 2 * (inner ℂ (d μ ν x) (d ν μ x)).re + ‖d ν μ x‖ ^ 2 :=
      fun μ ν => @norm_sub_sq ℂ _ _ _ _ _ _
    simp only [h1, sum_add_distrib, sum_sub_distrib]
    rw [sum_comm (f := fun μ ν => ‖d ν μ x‖ ^ 2)]
    simp only [← mul_sum]
    ring
  have e2 : ∀ x, ‖∑ μ, s μ x‖ ^ 2 = ∑ μ, ∑ ν, (inner ℂ (s μ x) (s ν x)).re := fun x => by
    rw [@norm_sq_eq_re_inner ℂ, sum_inner]
    simp only [inner_sum, map_sum]
    rfl
  simp only [e1, e2, sum_sub_distrib]
  -- the summation by parts
  have e3 : ∑ x, ∑ μ, ∑ ν, (inner ℂ (d μ ν x) (d ν μ x)).re = ∑ x, ∑ μ, ∑ ν, (inner ℂ (s μ x) (s ν x)).re := by
    have h : ∀ μ ν, ∑ x, (inner ℂ (d μ ν x) (d ν μ x)).re = ∑ x, (inner ℂ (s ν x) (s μ x)).re := fun μ ν => by
      rw [← Complex.re_sum, ← Complex.re_sum]
      congr 1
      exact sum_inner_swap S a μ ν
    calc _ = ∑ μ, ∑ ν, ∑ x, (inner ℂ (d μ ν x) (d ν μ x)).re := by
          rw [sum_comm]; exact sum_congr rfl fun _ _ => sum_comm
      _ = ∑ μ, ∑ ν, ∑ x, (inner ℂ (s ν x) (s μ x)).re := by simp only [h]
      _ = ∑ ν, ∑ μ, ∑ x, (inner ℂ (s ν x) (s μ x)).re := sum_comm
      _ = ∑ ν, ∑ x, ∑ μ, (inner ℂ (s ν x) (s μ x)).re := sum_congr rfl fun _ _ => sum_comm
      _ = _ := sum_comm
  rw [e3]
  ring

/-! ### The formula of Ismagilov, Morgan, and Simon -/

section IMS

variable {ι κ V : Type*} [Fintype ι] [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- A form with a kernel: `q(A) = Re Σ_{x,x'}⟨A(x), K(x, x')A(x')⟩`. -/
def qK (K : ι → ι → V →ₗ[ℂ] V) (A : ι → V) : ℝ := (∑ x, ∑ x', inner ℂ (A x) (K x x' (A x'))).re

omit [Fintype ι] in
lemma prod_sum_eq (s : Finset κ) (h : κ → ι → ℝ) (hs : ∀ x, ∑ c ∈ s, h c x ^ 2 = 1) (x x' : ι) :
    ∑ c ∈ s, h c x * h c x' = 1 - 1 / 2 * ∑ c ∈ s, (h c x - h c x') ^ 2 := by
  have e : ∀ c, (h c x - h c x') ^ 2 = h c x ^ 2 + h c x' ^ 2 - 2 * (h c x * h c x') := fun c => by ring
  simp only [e, sum_sub_distrib, sum_add_distrib, hs, ← mul_sum]
  ring

/-- **The formula of Ismagilov, Morgan, and Simon** for a form with a kernel. -/
theorem ims (s : Finset κ) (h : κ → ι → ℝ) (hs : ∀ x, ∑ c ∈ s, h c x ^ 2 = 1) (K : ι → ι → V →ₗ[ℂ] V) (A : ι → V) :
    ∑ c ∈ s, qK K (fun x => (h c x : ℂ) • A x) =
      qK K A - 1 / 2 * (∑ x, ∑ x', ((∑ c ∈ s, (h c x - h c x') ^ 2 : ℝ) : ℂ) * inner ℂ (A x) (K x x' (A x'))).re := by
  unfold qK
  have e1 : ∀ c, (∑ x, ∑ x', inner ℂ ((h c x : ℂ) • A x) (K x x' ((h c x' : ℂ) • A x'))) =
      ∑ x, ∑ x', ((h c x * h c x' : ℝ) : ℂ) * inner ℂ (A x) (K x x' (A x')) := fun c => by
    refine sum_congr rfl fun x _ => sum_congr rfl fun x' _ => ?_
    rw [map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    push_cast; ring
  simp only [e1]
  rw [← Complex.re_sum]
  rw [sum_comm (s := s)]
  have e2 : ∀ x x', ∑ c ∈ s, ((h c x * h c x' : ℝ) : ℂ) * inner ℂ (A x) (K x x' (A x')) =
      ((1 - 1 / 2 * ∑ c ∈ s, (h c x - h c x') ^ 2 : ℝ) : ℂ) * inner ℂ (A x) (K x x' (A x')) := fun x x' => by
    rw [← sum_mul, ← Complex.ofReal_sum, prod_sum_eq s h hs x x']
  simp only [Finset.sum_comm (s := s) (t := univ), e2]
  have e3 : ∀ x x', ((1 - 1 / 2 * ∑ c ∈ s, (h c x - h c x') ^ 2 : ℝ) : ℂ) * inner ℂ (A x) (K x x' (A x')) =
      inner ℂ (A x) (K x x' (A x')) -
        ((1 / 2 : ℝ) : ℂ) * (((∑ c ∈ s, (h c x - h c x') ^ 2 : ℝ) : ℂ) * inner ℂ (A x) (K x x' (A x'))) :=
    fun x x' => by push_cast; ring
  simp only [e3, sum_sub_distrib, ← mul_sum]
  rw [Complex.sub_re, Complex.re_ofReal_mul]

end IMS

end SFBounds
end CoreLean

end
