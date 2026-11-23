/-
The setting of `prop:interior-schauder` of BALABAN_CORE.tex (`a71f8998da10`): covariant differences on
`ηℤ⁴` at a configuration `𝐔 = e^{iη𝐚}`, transports along shortest paths, and the bound of the change of a
value by a transport.

* `Uf`, `Ub`: the transports `𝐔(n, n + e_μ) = e^{iη𝐚_μ(n)}` and `𝐔(n, n - e_μ) = 𝐔(n - e_μ, n)⁻¹`.
* `Dfw`, `Dbw`, `covLap`: `D_{𝐔,μ}`, `D^*_{𝐔,μ}` (`def:differences`) and `Δ_𝐔 = Σ_μ D^*_{𝐔,μ}D_{𝐔,μ}`.
* `pathT`: the transport `𝐔(γ)` along the path which starts at `x` and takes the steps `sgn(m_μ)e_μ` in the
  order of a list of coordinates; `IsShortest x x' l`: the list has `|x'_μ - x_μ|` entries `μ`, so that the path
  is a shortest path from `x` to `x'` (every shortest lattice path is of this form). `WalkIn`, `walkIn_box`: the
  points of a shortest path lie in the box spanned by its ends.
* `norm_Ad_pathT_sub_le`: if every bond of the path changes a value by at most `δ` times its norm, the path
  changes it by at most `((1 + δ)^m - 1)` times its norm, `m` the number of steps.
-/
import CoreLean.FreeSchauder
import CoreLean.ProductExp

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace CoreLean
namespace InteriorSchauder

variable {N : ℕ}

local notation "Mat" => Matrix (Fin N) (Fin N) ℂ
local notation "GLN" => (Matrix (Fin N) (Fin N) ℂ)ˣ

/-- The transport along the positive bond `(n, n + e_μ)`: `e^{iη𝐚_μ(n)}`. -/
def Uf (η : ℝ) (A : Fin 4 → (Fin 4 → ℤ) → Mat) (μ : Fin 4) (n : Fin 4 → ℤ) : GLN :=
  expU (Complex.I • (η • A μ n))

/-- The transport along the negative bond `(n, n - e_μ)`: `𝐔(n - e_μ, n)⁻¹ = e^{-iη𝐚_μ(n - e_μ)}`. -/
def Ub (η : ℝ) (A : Fin 4 → (Fin 4 → ℤ) → Mat) (μ : Fin 4) (n : Fin 4 → ℤ) : GLN :=
  expU (Complex.I • (-(η • A μ (n - e4 μ))))

/-- `(D_{𝐔,μ}f)(n) = η⁻¹(Ad_{𝐔(n, n + e_μ)}f(n + e_μ) - f(n))`. -/
def Dfw (η : ℝ) (A : Fin 4 → (Fin 4 → ℤ) → Mat) (μ : Fin 4) (f : (Fin 4 → ℤ) → Mat) (n : Fin 4 → ℤ) : Mat :=
  η⁻¹ • (Ad (Uf η A μ n) (f (n + e4 μ)) - f n)

/-- `(D^*_{𝐔,μ}f)(n) = η⁻¹(Ad_{𝐔(n, n - e_μ)}f(n - e_μ) - f(n))`. -/
def Dbw (η : ℝ) (A : Fin 4 → (Fin 4 → ℤ) → Mat) (μ : Fin 4) (f : (Fin 4 → ℤ) → Mat) (n : Fin 4 → ℤ) : Mat :=
  η⁻¹ • (Ad (Ub η A μ n) (f (n - e4 μ)) - f n)

/-- The covariant Laplacian `Δ_𝐔 = Σ_μ D^*_{𝐔,μ}D_{𝐔,μ}`. -/
def covLap (η : ℝ) (A : Fin 4 → (Fin 4 → ℤ) → Mat) (f : (Fin 4 → ℤ) → Mat) (n : Fin 4 → ℤ) : Mat :=
  ∑ μ, Dbw η A μ (Dfw η A μ f) n

/-- The transport back along a bond undoes the transport forward. -/
lemma Ad_Ub_Ad_Uf (η : ℝ) (A : Fin 4 → (Fin 4 → ℤ) → Mat) (μ : Fin 4) (n : Fin 4 → ℤ) (Z : Mat) :
    Ad (Ub η A μ (n + e4 μ)) (Ad (Uf η A μ n) Z) = Z := by
  rw [Ub, Uf, add_sub_cancel_right, smul_neg, ← expU_inv, Ad_inv_Ad]

/-! ### The bounds along one bond -/

lemma norm_Ad_Uf_sub_le {η a : ℝ} (hη : 0 < η) (hηa : η ≤ a) {A : Fin 4 → (Fin 4 → ℤ) → Mat} {μ : Fin 4}
    {n : Fin 4 → ℤ} (hA : a * ‖A μ n‖ ≤ 1 / 32) (Z : Mat) :
    ‖Ad (Uf η A μ n) Z - Z‖ ≤ 6 * (η * ‖A μ n‖) * ‖Z‖ := by
  have ha : 0 < a := hη.trans_le hηa
  have hX : ‖η • A μ n‖ ≤ 1 / 32 := by
    rw [norm_smul, Real.norm_of_nonneg hη.le]
    calc η * ‖A μ n‖ ≤ a * ‖A μ n‖ := mul_le_mul_of_nonneg_right hηa (norm_nonneg _)
      _ ≤ 1 / 32 := hA
  have := norm_Ad_exp_sub_le hX Z
  rwa [norm_smul, Real.norm_of_nonneg hη.le] at this

lemma norm_Ad_Ub_sub_le {η a : ℝ} (hη : 0 < η) (hηa : η ≤ a) {A : Fin 4 → (Fin 4 → ℤ) → Mat} {μ : Fin 4}
    {n : Fin 4 → ℤ} (hA : a * ‖A μ (n - e4 μ)‖ ≤ 1 / 32) (Z : Mat) :
    ‖Ad (Ub η A μ n) Z - Z‖ ≤ 6 * (η * ‖A μ (n - e4 μ)‖) * ‖Z‖ := by
  have hX : ‖-(η • A μ (n - e4 μ))‖ ≤ 1 / 32 := by
    rw [norm_neg, norm_smul, Real.norm_of_nonneg hη.le]
    calc η * ‖A μ (n - e4 μ)‖ ≤ a * ‖A μ (n - e4 μ)‖ := mul_le_mul_of_nonneg_right hηa (norm_nonneg _)
      _ ≤ 1 / 32 := hA
  have := norm_Ad_exp_sub_le hX Z
  rwa [norm_neg, norm_smul, Real.norm_of_nonneg hη.le] at this

/-- With `a‖𝐚‖ ≤ 1/32`, a bond changes a value by at most `η/(4a)` times its norm. -/
lemma norm_Ad_Uf_sub_le' {η a : ℝ} (hη : 0 < η) (hηa : η ≤ a) {A : Fin 4 → (Fin 4 → ℤ) → Mat} {μ : Fin 4}
    {n : Fin 4 → ℤ} (hA : a * ‖A μ n‖ ≤ 1 / 32) (Z : Mat) :
    ‖Ad (Uf η A μ n) Z - Z‖ ≤ η / (4 * a) * ‖Z‖ := by
  have ha : 0 < a := hη.trans_le hηa
  refine (norm_Ad_Uf_sub_le hη hηa hA Z).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  rw [le_div_iff₀ (by positivity)]
  nlinarith [norm_nonneg (A μ n)]

lemma norm_Ad_Ub_sub_le' {η a : ℝ} (hη : 0 < η) (hηa : η ≤ a) {A : Fin 4 → (Fin 4 → ℤ) → Mat} {μ : Fin 4}
    {n : Fin 4 → ℤ} (hA : a * ‖A μ (n - e4 μ)‖ ≤ 1 / 32) (Z : Mat) :
    ‖Ad (Ub η A μ n) Z - Z‖ ≤ η / (4 * a) * ‖Z‖ := by
  have ha : 0 < a := hη.trans_le hηa
  refine (norm_Ad_Ub_sub_le hη hηa hA Z).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  rw [le_div_iff₀ (by positivity)]
  nlinarith [norm_nonneg (A μ (n - e4 μ))]

/-! ### Shortest paths and their transports -/

/-- The transport along a bond in the direction `s_μ e_μ`, `s_μ ∈ {1, -1}`. -/
def bondT (η : ℝ) (A : Fin 4 → (Fin 4 → ℤ) → Mat) (s : Fin 4 → ℤ) (μ : Fin 4) (x : Fin 4 → ℤ) : GLN :=
  if 0 ≤ s μ then Uf η A μ x else Ub η A μ x

/-- The transport `𝐔(γ)` along the path from `x` with the steps `s_μ e_μ` in the order of the list. -/
def pathT (η : ℝ) (A : Fin 4 → (Fin 4 → ℤ) → Mat) (s : Fin 4 → ℤ) : (Fin 4 → ℤ) → List (Fin 4) → GLN
  | _, [] => 1
  | x, μ :: l => bondT η A s μ x * pathT η A s (x + s μ • e4 μ) l

/-- A property of all the points of the path, with the next point of each. -/
def WalkIn (s : Fin 4 → ℤ) (P : (Fin 4 → ℤ) → Fin 4 → Prop) : (Fin 4 → ℤ) → List (Fin 4) → Prop
  | _, [] => True
  | x, μ :: l => P x μ ∧ WalkIn s P (x + s μ • e4 μ) l

lemma WalkIn.mono {s : Fin 4 → ℤ} {P P' : (Fin 4 → ℤ) → Fin 4 → Prop} (h : ∀ p μ, P p μ → P' p μ) :
    ∀ (l : List (Fin 4)) (x : Fin 4 → ℤ), WalkIn s P x l → WalkIn s P' x l
  | [], _, _ => trivial
  | _ :: l, _, ⟨h1, h2⟩ => ⟨h _ _ h1, WalkIn.mono h l _ h2⟩

/-- The end of the path. -/
def walkEnd (s : Fin 4 → ℤ) : (Fin 4 → ℤ) → List (Fin 4) → (Fin 4 → ℤ)
  | x, [] => x
  | x, μ :: l => walkEnd s (x + s μ • e4 μ) l

lemma walkEnd_eq (s : Fin 4 → ℤ) : ∀ (l : List (Fin 4)) (x : Fin 4 → ℤ),
    walkEnd s x l = x + fun μ => s μ * l.count μ
  | [], x => by funext μ; simp [walkEnd]
  | ν :: l, x => by
    rw [walkEnd, walkEnd_eq s l]
    funext μ
    simp only [Pi.add_apply, Pi.smul_apply, e4, List.count_cons]
    by_cases h : μ = ν
    · subst h; simp; ring
    · simp [Pi.single_eq_of_ne h, Ne.symm h]

/-- A function which changes by at most `c` along every step changes by at most `c` times the number of steps. -/
lemma norm_sub_le_walk {F : Type*} [SeminormedAddCommGroup F] (s : Fin 4 → ℤ) (g : (Fin 4 → ℤ) → F) {c : ℝ} :
    ∀ (l : List (Fin 4)) (x : Fin 4 → ℤ), WalkIn s (fun p μ => ‖g (p + s μ • e4 μ) - g p‖ ≤ c) x l →
      ‖g (walkEnd s x l) - g x‖ ≤ c * l.length
  | [], x, _ => by simp [walkEnd]
  | μ :: l, x, ⟨h1, h2⟩ => by
    have ih := norm_sub_le_walk s g l _ h2
    rw [walkEnd, List.length_cons, Nat.cast_succ]
    calc ‖g (walkEnd s (x + s μ • e4 μ) l) - g x‖ ≤
        ‖g (walkEnd s (x + s μ • e4 μ) l) - g (x + s μ • e4 μ)‖ + ‖g (x + s μ • e4 μ) - g x‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ c * l.length + c := add_le_add ih h1
      _ = c * (l.length + 1) := by ring

/-- The signs of the steps of a shortest path from `x` to `x'`. -/
def sgnv (x x' : Fin 4 → ℤ) : Fin 4 → ℤ := fun μ => Int.sign (x' μ - x μ)

/-- A shortest path from `x` to `x'`: `|x'_μ - x_μ|` steps `sgn(x'_μ - x_μ)e_μ` in every direction `μ`. -/
def IsShortest (x x' : Fin 4 → ℤ) (l : List (Fin 4)) : Prop := ∀ μ, l.count μ = (x' μ - x μ).natAbs

lemma walkEnd_shortest {x x' : Fin 4 → ℤ} {l : List (Fin 4)} (h : IsShortest x x' l) :
    walkEnd (sgnv x x') x l = x' := by
  rw [walkEnd_eq]
  funext μ
  simp only [Pi.add_apply, sgnv, h μ, Int.natCast_natAbs, Int.sign_mul_abs, add_sub_cancel]


/-- The box spanned by `x` and `x + s_μ c_μ e_μ`. -/
def InBox (x : Fin 4 → ℤ) (s : Fin 4 → ℤ) (c : Fin 4 → ℕ) (p : Fin 4 → ℤ) : Prop :=
  ∀ μ, min (x μ) (x μ + s μ * c μ) ≤ p μ ∧ p μ ≤ max (x μ) (x μ + s μ * c μ)

lemma inBox_start (x : Fin 4 → ℤ) (s : Fin 4 → ℤ) (c : Fin 4 → ℕ) : InBox x s c x := fun _ =>
  ⟨min_le_left _ _, le_max_left _ _⟩

/-- The points of a path with `c_μ` steps `s_μ e_μ` lie in the box spanned by its ends. -/
theorem walkIn_box (s : Fin 4 → ℤ) (hs : ∀ μ, s μ = 1 ∨ s μ = -1 ∨ s μ = 0) :
    ∀ (l : List (Fin 4)) (x : Fin 4 → ℤ), (∀ μ, s μ = 0 → l.count μ = 0) →
      WalkIn s (fun p μ => InBox x s (fun μ => l.count μ) p ∧
        InBox x s (fun μ => l.count μ) (p + s μ • e4 μ) ∧ s μ ≠ 0) x l := by
  -- a stronger statement: the box of the tail lies in the box of the whole path
  have key : ∀ (l : List (Fin 4)) (x : Fin 4 → ℤ) (B : (Fin 4 → ℤ) → Prop),
      (∀ μ, s μ = 0 → l.count μ = 0) → (∀ p, InBox x s (fun μ => l.count μ) p → B p) →
      WalkIn s (fun p μ => B p ∧ B (p + s μ • e4 μ) ∧ s μ ≠ 0) x l := by
    intro l
    induction l with
    | nil => intro x B _ _; trivial
    | cons μ0 l ih =>
      intro x B h0 hB
      have hμ0 : s μ0 ≠ 0 := by
        intro h; have := h0 μ0 h; simp at this
      have hsub : ∀ p, InBox (x + s μ0 • e4 μ0) s (fun μ => l.count μ) p →
          InBox x s (fun μ => (μ0 :: l).count μ) p := by
        intro p hp μ
        obtain ⟨h1, h2⟩ := hp μ
        by_cases hμ : μ = μ0
        · subst hμ
          simp only [List.count_cons_self, Pi.add_apply, Pi.smul_apply, e4, Pi.single_eq_same,
            smul_eq_mul, mul_one] at h1 h2 ⊢
          push_cast at h1 h2 ⊢
          rcases hs μ with h | h | h
          · rw [h] at h1 h2 ⊢
            constructor <;> [skip; skip] <;>
              · simp only [min_def, max_def] at h1 h2 ⊢
                split_ifs at h1 h2 ⊢ <;> omega
          · rw [h] at h1 h2 ⊢
            constructor <;>
              · simp only [min_def, max_def] at h1 h2 ⊢
                split_ifs at h1 h2 ⊢ <;> omega
          · exact absurd h hμ0
        · have hc : (μ0 :: l).count μ = l.count μ := by
            rw [List.count_cons]; simp [Ne.symm hμ]
          simp only [Pi.add_apply, Pi.smul_apply, e4, Pi.single_eq_of_ne hμ, smul_zero, add_zero] at h1 h2
          dsimp only
          rw [hc]
          exact ⟨h1, h2⟩
      refine ⟨⟨hB x (inBox_start _ _ _), hB _ (hsub _ (inBox_start _ _ _)), hμ0⟩, ?_⟩
      refine ih _ B (fun μ h => ?_) fun p hp => hB p (hsub p hp)
      have := h0 μ h
      rw [List.count_cons] at this
      omega
  intro l x h0
  exact key l x _ h0 fun p hp => hp

/-- The change of a value by the transport along a path whose bonds each change a value by at most `δ` times
its norm. -/
theorem norm_Ad_pathT_sub_le (η : ℝ) (A : Fin 4 → (Fin 4 → ℤ) → Mat) (s : Fin 4 → ℤ) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∀ (l : List (Fin 4)) (x : Fin 4 → ℤ),
      WalkIn s (fun p μ => ∀ Z, ‖Ad (bondT η A s μ p) Z - Z‖ ≤ δ * ‖Z‖) x l →
      ∀ Z : Mat, ‖Ad (pathT η A s x l) Z - Z‖ ≤ ((1 + δ) ^ l.length - 1) * ‖Z‖
  | [], x, _, Z => by simp [pathT, Ad]
  | μ :: l, x, h, Z => by
    obtain ⟨h1, h2⟩ := h
    have ih := norm_Ad_pathT_sub_le η A s hδ l _ h2 Z
    have hT : ‖Ad (pathT η A s (x + s μ • e4 μ) l) Z‖ ≤ (1 + δ) ^ l.length * ‖Z‖ := by
      have := norm_sub_norm_le (Ad (pathT η A s (x + s μ • e4 μ) l) Z) Z
      nlinarith [norm_nonneg Z]
    rw [pathT, Ad_mul]
    have hb := h1 (Ad (pathT η A s (x + s μ • e4 μ) l) Z)
    calc ‖Ad (bondT η A s μ x) (Ad (pathT η A s (x + s μ • e4 μ) l) Z) - Z‖
        ≤ ‖Ad (bondT η A s μ x) (Ad (pathT η A s (x + s μ • e4 μ) l) Z) -
            Ad (pathT η A s (x + s μ • e4 μ) l) Z‖ + ‖Ad (pathT η A s (x + s μ • e4 μ) l) Z - Z‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ δ * ((1 + δ) ^ l.length * ‖Z‖) + ((1 + δ) ^ l.length - 1) * ‖Z‖ := by
          gcongr
          exact hb.trans (mul_le_mul_of_nonneg_left hT hδ)
      _ = ((1 + δ) ^ (μ :: l).length - 1) * ‖Z‖ := by rw [List.length_cons, pow_succ]; ring

/-- `(1 + δ)^m - 1 ≤ 2mδ` for `mδ ≤ 1`. -/
lemma one_add_pow_sub_one_le {δ : ℝ} (hδ : 0 ≤ δ) {m : ℕ} (hm : m * δ ≤ 1) : (1 + δ) ^ m - 1 ≤ 2 * (m * δ) := by
  have h1 : (1 + δ) ^ m ≤ Real.exp (m * δ) := by
    calc (1 + δ) ^ m ≤ Real.exp δ ^ m := pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp δ]) m
      _ = Real.exp (m * δ) := by rw [← Real.exp_nat_mul]
  have hm0 : 0 ≤ (m : ℝ) * δ := mul_nonneg (Nat.cast_nonneg m) hδ
  have h2 := Real.abs_exp_sub_one_le (x := m * δ) (by rw [abs_of_nonneg hm0]; exact hm)
  rw [abs_of_nonneg hm0, abs_of_nonneg (by have := Real.add_one_le_exp (m * δ); linarith)] at h2
  linarith

/-- A shortest path from `x` to `x'` exists. -/
lemma exists_shortest (x x' : Fin 4 → ℤ) : ∃ l, IsShortest x x' l := by
  refine ⟨List.replicate (x' 0 - x 0).natAbs 0 ++ List.replicate (x' 1 - x 1).natAbs 1 ++
    List.replicate (x' 2 - x 2).natAbs 2 ++ List.replicate (x' 3 - x 3).natAbs 3, fun μ => ?_⟩
  fin_cases μ <;> simp [List.count_append, List.count_replicate]

lemma length_of_shortest {x x' : Fin 4 → ℤ} {l : List (Fin 4)} (h : IsShortest x x' l) :
    l.length = ∑ μ, (x' μ - x μ).natAbs := by
  have := Multiset.sum_count_eq_card (s := Finset.univ) (m := (l : Multiset (Fin 4)))
    (fun a _ => Finset.mem_univ a)
  simp only [Multiset.coe_count, Multiset.coe_card] at this
  rw [← this]
  exact Finset.sum_congr rfl fun μ _ => h μ

end InteriorSchauder
end CoreLean

end
