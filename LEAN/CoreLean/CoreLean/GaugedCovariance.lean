/-
`lem:gauged-covariance` of BALABAN_CORE.tex (`a021c13be348`), its proof in abstract form. Configurations are
functions on a set of bonds `b` with ends `b₋ = src b`, `b₊ = tgt b`, with values in a group `G`; a gauge
transformation `k` acts by `W^k(b) = k(b₋)W(b)k(b₊)⁻¹` (`gauge`), and the move by a `1`-form `H` with values in a
space with an adjoint action is `(e^{ia₀H}W)(b) = e^{ia₀H(b)}W(b)`, with an exponential which satisfies
`exp(Ad_k X) = k exp(X) k⁻¹`.

* `(e^{ia₀𝐇'}𝐖)^k = e^{ia₀𝐇}𝐖^k` for `𝐇 = Ad_k𝐇'` (`move_gauge`), and `(W^k)^g = W^{gk}` (`gauge_gauge`).
* The transformation of the gauged move (`eq:gauged-move`) along a chain `x_j = y, x_{j-1}, …, x_0` of a block:
  if the site factors and the transports are covariant, `v' = k(y)vk(y)⁻¹` and
  `T'_n = k(x_{n+1})T_nk(x_n)⁻¹`, then `g'(x_n) = k(y)g(x_n)k(x_n)⁻¹` for `n ≤ j` (`chain_covariance`).
* With this identity at every point, `𝒢(𝐇; 𝐖^k) = 𝒢(𝐇'; 𝐖)^{k̄}`, `k̄(x) = k(y)` on the block of `y`
  (`gauged_covariance`, `eq:gauged-covariance`).

The hypotheses of the lemma (the moves are defined, and the averages, their transports along the chains, and the
site factors are covariant under `k`) are the hypotheses here.
-/
import Mathlib

noncomputable section

namespace CoreLean
namespace GaugedCovariance

variable {G A X B : Type*} [Group G] [MulAction G A]

/-- The gauge action `W^k(b) = k(b₋)W(b)k(b₊)⁻¹`. -/
def gauge (src tgt : B → X) (W : B → G) (k : X → G) : B → G := fun b => k (src b) * W b * (k (tgt b))⁻¹

/-- The move `(e^{ia₀H}W)(b) = e^{ia₀H(b)}W(b)`. -/
def move (exp : A → G) (H : B → A) (W : B → G) : B → G := fun b => exp (H b) * W b

variable (src tgt : B → X)

/-- `(e^{ia₀𝐇'}𝐖)^k = e^{ia₀𝐇}𝐖^k` for `𝐇 = Ad_k𝐇'`. -/
theorem move_gauge (exp : A → G) (hexp : ∀ (k : G) (Y : A), exp (k • Y) = k * exp Y * k⁻¹) (H' : B → A)
    (W : B → G) (k : X → G) :
    gauge src tgt (move exp H' W) k = move exp (fun b => k (src b) • H' b) (gauge src tgt W k) := by
  funext b
  simp only [gauge, move, hexp]
  group

/-- `(W^k)^g = W^{gk}`. -/
theorem gauge_gauge (W : B → G) (k g : X → G) :
    gauge src tgt (gauge src tgt W k) g = gauge src tgt W (fun x => g x * k x) := by
  funext b
  simp only [gauge]
  group

/-- **The transformations along a chain**: `g'(x_n) = k(y)g(x_n)k(x_n)⁻¹`. -/
theorem chain_covariance (c : ℕ → X) (j : ℕ) (g g' k : X → G) (v : G) (T T' : ℕ → G)
    (hg : g (c j) = v⁻¹) (hg' : g' (c j) = (k (c j) * v * (k (c j))⁻¹)⁻¹)
    (hrec : ∀ n < j, g (c n) = g (c (n + 1)) * T n) (hrec' : ∀ n < j, g' (c n) = g' (c (n + 1)) * T' n)
    (hT : ∀ n < j, T' n = k (c (n + 1)) * T n * (k (c n))⁻¹) :
    ∀ n ≤ j, g' (c n) = k (c j) * g (c n) * (k (c n))⁻¹ := by
  -- induction on `m = j - n`
  have key : ∀ m ≤ j, g' (c (j - m)) = k (c j) * g (c (j - m)) * (k (c (j - m)))⁻¹ := by
    intro m
    induction m with
    | zero => intro _; simp only [Nat.sub_zero, hg, hg']; group
    | succ m ih =>
      intro hm
      have hn : j - (m + 1) < j := by omega
      have e : j - (m + 1) + 1 = j - m := by omega
      rw [hrec' _ hn, hrec _ hn, hT _ hn, e, ih (by omega)]
      group
  intro n hn
  have := key (j - n) (Nat.sub_le _ _)
  rwa [Nat.sub_sub_self hn] at this

/-- **`eq:gauged-covariance`**: `𝒢(𝐇; 𝐖^k) = 𝒢(𝐇'; 𝐖)^{k̄}`. -/
theorem gauged_covariance (exp : A → G) (hexp : ∀ (k : G) (Y : A), exp (k • Y) = k * exp Y * k⁻¹)
    (H' : B → A) (W : B → G) (k g g' kbar : X → G) (hchain : ∀ x, g' x * k x = kbar x * g x) :
    gauge src tgt (move exp (fun b => k (src b) • H' b) (gauge src tgt W k)) g' =
      gauge src tgt (gauge src tgt (move exp H' W) g) kbar := by
  rw [← move_gauge src tgt exp hexp, gauge_gauge, gauge_gauge]
  congr 1
  funext x
  exact hchain x

/-- The identity of `chain_covariance` gives the hypothesis of `gauged_covariance`. -/
lemma chain_to_pointwise {g g' k : X → G} {y x : X} (h : g' x = k y * g x * (k x)⁻¹) :
    g' x * k x = k y * g x := by
  rw [h]; group

end GaugedCovariance
end CoreLean

end
