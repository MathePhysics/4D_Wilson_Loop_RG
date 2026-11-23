/-
`lem:ward`(ii), (iii): the triviality of the centre gives `𝔤^c = [𝔤^c, 𝔤^c]`.

For `G ⊂ U(N)` the Lie algebra, in the convention `e^{iλ}`, is a real subspace `𝔤` of the hermitian
`N × N` matrices closed under `-i[·, ·]`; its complexification is `𝔤^c = span_ℂ 𝔤 = 𝔤 + i𝔤`. If the centre
of `𝔤` is trivial, so is that of `𝔤^c`, and the commutators span `𝔤^c`: the trace form `(w, s) ↦ tr(ws)` maps
`𝔤^c` injectively into the dual of `S = span[𝔤^c, 𝔤^c]`, because `tr(w[a, c]) = tr([w, a]c)` vanishes for
`c = [w, a]ᴴ` only if `[w, a] = 0`; so `dim 𝔤^c ≤ dim S` and `S = 𝔤^c`. This is the form `Perfect` in which
`WardIdentities.lean` uses the hypothesis (the core: "the value of `E^{(1)}` at each bond commutes with
`𝔤^c` and vanishes when the centre is trivial").
-/
import CoreLean.WardIdentities

open Matrix
open scoped ComplexOrder

noncomputable section

namespace CoreLean

namespace Ward

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Lie algebra of `G ⊂ U(N)` in the convention `e^{iλ}`: hermitian matrices, closed under
`-i[·, ·]`, with a trivial centre. -/
structure HermLie (n : Type*) [Fintype n] [DecidableEq n] where
  g : Submodule ℝ (Matrix n n ℂ)
  herm : ∀ x ∈ g, xᴴ = x
  lie : ∀ x ∈ g, ∀ y ∈ g, (-Complex.I) • (x * y - y * x) ∈ g
  centre : ∀ x ∈ g, (∀ y ∈ g, x * y = y * x) → x = 0

namespace HermLie

variable (H : HermLie n)

/-- `𝔤^c = span_ℂ 𝔤`. -/
def gc : Submodule ℂ (Matrix n n ℂ) := Submodule.span ℂ (H.g : Set (Matrix n n ℂ))

lemma real_smul_eq (r : ℝ) (x : Matrix n n ℂ) : (r : ℂ) • x = r • x := by
  ext i j; simp [Complex.real_smul]

lemma mem_gc_of_mem {x : Matrix n n ℂ} (hx : x ∈ H.g) : x ∈ H.gc := Submodule.subset_span hx

/-- `𝔤^c = 𝔤 + i𝔤`. -/
lemma mem_gc_iff {v : Matrix n n ℂ} :
    v ∈ H.gc ↔ ∃ μ ∈ H.g, ∃ ν ∈ H.g, v = μ + Complex.I • ν := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem x hx => exact ⟨x, hx, 0, H.g.zero_mem, by simp⟩
    | zero => exact ⟨0, H.g.zero_mem, 0, H.g.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨μ, hμ, ν, hν, rfl⟩ := hx
      obtain ⟨μ', hμ', ν', hν', rfl⟩ := hy
      exact ⟨μ + μ', H.g.add_mem hμ hμ', ν + ν', H.g.add_mem hν hν', by rw [smul_add]; abel⟩
    | smul c x _ hx =>
      obtain ⟨μ, hμ, ν, hν, rfl⟩ := hx
      refine ⟨c.re • μ - c.im • ν, H.g.sub_mem (H.g.smul_mem _ hμ) (H.g.smul_mem _ hν),
        c.im • μ + c.re • ν, H.g.add_mem (H.g.smul_mem _ hμ) (H.g.smul_mem _ hν), ?_⟩
      ext i j
      simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul,
        Complex.real_smul]
      apply Complex.ext <;> simp <;> ring
  · rintro ⟨μ, hμ, ν, hν, rfl⟩
    exact H.gc.add_mem (H.mem_gc_of_mem hμ) (H.gc.smul_mem _ (H.mem_gc_of_mem hν))

lemma star_mem {v : Matrix n n ℂ} (hv : v ∈ H.gc) : vᴴ ∈ H.gc := by
  obtain ⟨μ, hμ, ν, hν, rfl⟩ := (H.mem_gc_iff).mp hv
  refine (H.mem_gc_iff).mpr ⟨μ, hμ, -ν, H.g.neg_mem hν, ?_⟩
  rw [conjTranspose_add, conjTranspose_smul, H.herm μ hμ, H.herm ν hν, Complex.star_def,
    Complex.conj_I, smul_neg, neg_smul]

lemma com_mem_of_g {x y : Matrix n n ℂ} (hx : x ∈ H.g) (hy : y ∈ H.g) : x * y - y * x ∈ H.gc := by
  have h := H.gc.smul_mem Complex.I (H.mem_gc_of_mem (H.lie x hx y hy))
  rwa [smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul] at h

/-- `𝔤^c` is closed under commutators. -/
lemma lie_mem {a c : Matrix n n ℂ} (ha : a ∈ H.gc) (hc : c ∈ H.gc) : a * c - c * a ∈ H.gc := by
  obtain ⟨μ, hμ, ν, hν, rfl⟩ := (H.mem_gc_iff).mp ha
  obtain ⟨μ', hμ', ν', hν', rfl⟩ := (H.mem_gc_iff).mp hc
  have e : (μ + Complex.I • ν) * (μ' + Complex.I • ν') - (μ' + Complex.I • ν') * (μ + Complex.I • ν) =
      (μ * μ' - μ' * μ) + Complex.I • (μ * ν' - ν' * μ) + Complex.I • (ν * μ' - μ' * ν) +
        (Complex.I * Complex.I) • (ν * ν' - ν' * ν) := by
    simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub]
    module
  rw [e]
  exact H.gc.add_mem (H.gc.add_mem (H.gc.add_mem (H.com_mem_of_g hμ hμ')
    (H.gc.smul_mem _ (H.com_mem_of_g hμ hν'))) (H.gc.smul_mem _ (H.com_mem_of_g hν hμ')))
    (H.gc.smul_mem _ (H.com_mem_of_g hν hν'))

/-- The centre of `𝔤^c` is trivial. -/
lemma centre_gc {w : Matrix n n ℂ} (hw : w ∈ H.gc) (hcomm : ∀ a ∈ H.gc, w * a = a * w) : w = 0 := by
  obtain ⟨μ, hμ, ν, hν, rfl⟩ := (H.mem_gc_iff).mp hw
  have key : ∀ y ∈ H.g, μ * y = y * μ ∧ ν * y = y * ν := by
    intro y hy
    have h0 := hcomm y (H.mem_gc_of_mem hy)
    -- `[μ, y] + i[ν, y] = 0`, and its conjugate transpose `-[μ, y] + i[ν, y] = 0`
    have h1 : (μ * y - y * μ) + Complex.I • (ν * y - y * ν) = 0 := by
      calc (μ * y - y * μ) + Complex.I • (ν * y - y * ν)
          = (μ + Complex.I • ν) * y - y * (μ + Complex.I • ν) := by
            simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_sub]
            abel
        _ = 0 := sub_eq_zero.mpr h0
    have h2 := congrArg conjTranspose h1
    rw [conjTranspose_add, conjTranspose_smul, conjTranspose_sub, conjTranspose_sub,
      conjTranspose_mul, conjTranspose_mul, conjTranspose_mul, conjTranspose_mul, H.herm μ hμ,
      H.herm ν hν, H.herm y hy, Complex.star_def, Complex.conj_I, conjTranspose_zero] at h2
    have hμy : μ * y - y * μ = 0 := by
      have : (2 : ℂ) • (μ * y - y * μ) = 0 := by
        rw [two_smul]
        calc (μ * y - y * μ) + (μ * y - y * μ)
            = ((μ * y - y * μ) + Complex.I • (ν * y - y * ν)) -
                ((y * μ - μ * y) + -Complex.I • (y * ν - ν * y)) := by
              simp only [neg_smul, smul_sub]; abel
          _ = 0 := by rw [h1, h2, sub_zero]
      exact (smul_eq_zero.mp this).resolve_left two_ne_zero
    have hνy : ν * y - y * ν = 0 := by
      rw [hμy, zero_add] at h1
      exact (smul_eq_zero.mp h1).resolve_left Complex.I_ne_zero
    exact ⟨sub_eq_zero.mp hμy, sub_eq_zero.mp hνy⟩
  rw [H.centre μ hμ fun y hy => (key y hy).1, H.centre ν hν fun y hy => (key y hy).2]
  simp

/-- `tr(AAᴴ) = 0` only for `A = 0`. -/
lemma eq_zero_of_trace_mul_conjTranspose {A : Matrix n n ℂ} (h : trace (A * Aᴴ) = 0) : A = 0 := by
  have := (trace_conjTranspose_mul_self_eq_zero_iff (A := Aᴴ)).mp (by simpa using h)
  simpa using congrArg conjTranspose this

/-- The trivial centre gives `𝔤^c = [𝔤^c, 𝔤^c]`, the hypothesis `Perfect` of `WardIdentities.lean`. -/
theorem perfect :
    ∀ v ∈ H.gc, v ∈ Submodule.span ℂ {w | ∃ a ∈ H.gc, ∃ c ∈ H.gc, w = a * c - c * a} := by
  set S := Submodule.span ℂ {w : Matrix n n ℂ | ∃ a ∈ H.gc, ∃ c ∈ H.gc, w = a * c - c * a}
  have hS : S ≤ H.gc := by
    refine Submodule.span_le.mpr ?_
    rintro w ⟨a, ha, c, hc, rfl⟩
    exact H.lie_mem ha hc
  -- the trace form from `𝔤^c` to the dual of `S`
  let ψ : H.gc →ₗ[ℂ] Module.Dual ℂ S := LinearMap.mk₂ ℂ
    (fun (w : H.gc) (s : S) => trace ((w : Matrix n n ℂ) * (s : Matrix n n ℂ)))
    (fun w w' s => by simp [add_mul, trace_add])
    (fun c w s => by simp [smul_mul_assoc, trace_smul])
    (fun w s s' => by simp [mul_add, trace_add])
    (fun c w s => by simp [mul_smul_comm, trace_smul])
  have hinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro w hw
    have hw0 : ∀ s ∈ S, trace ((w : Matrix n n ℂ) * s) = 0 := fun s hs => by
      have := LinearMap.congr_fun (LinearMap.mem_ker.mp hw) ⟨s, hs⟩
      simpa [ψ] using this
    have hcomm : ∀ a ∈ H.gc, (w : Matrix n n ℂ) * a = a * w := by
      intro a ha
      set D := (w : Matrix n n ℂ) * a - a * w
      have hD : D ∈ H.gc := H.lie_mem w.2 ha
      have htr : trace (D * Dᴴ) = 0 := by
        have h1 := hw0 (a * Dᴴ - Dᴴ * a) (Submodule.subset_span ⟨a, ha, Dᴴ, H.star_mem hD, rfl⟩)
        -- `tr(w(aDᴴ - Dᴴa)) = tr((wa - aw)Dᴴ)`, since `tr(wDᴴa) = tr(awDᴴ)`
        have e : trace ((w : Matrix n n ℂ) * (a * Dᴴ - Dᴴ * a)) = trace (D * Dᴴ) := by
          simp only [D, mul_sub, sub_mul, trace_sub, ← mul_assoc]
          rw [trace_mul_cycle (w : Matrix n n ℂ) Dᴴ a]
        rwa [e] at h1
      exact sub_eq_zero.mp (eq_zero_of_trace_mul_conjTranspose htr)
    exact Subtype.ext (H.centre_gc w.2 hcomm)
  have hle : Module.finrank ℂ H.gc ≤ Module.finrank ℂ S := by
    calc Module.finrank ℂ H.gc ≤ Module.finrank ℂ (Module.Dual ℂ S) :=
          LinearMap.finrank_le_finrank_of_injective hinj
      _ = Module.finrank ℂ S := Subspace.dual_finrank_eq
  have heq : S = H.gc := Submodule.eq_of_le_of_finrank_le hS hle
  intro v hv
  rw [heq]
  exact hv

end HermLie

end Ward

end CoreLean
