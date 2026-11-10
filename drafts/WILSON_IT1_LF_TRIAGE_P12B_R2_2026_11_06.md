# Packet 12b r2 Triage (LF #3.63–#3.100-1)

## The Report of r2

r2 (lf-p12b-20261106-r2, run under .claude-Main) found no fatal finding, no serious finding, and eight minor ones. All thirteen first-round findings are repaired, and the verdict is that the claim holds. So r2 is not clean, and r3 is a full round. Each finding was re-derived and repaired in place.

| Finding | Item | Repair |
|---|---|---|
| m1 | #3.77 | At α = 1/12 the leading term is ½(1 + κ_s) + 2α = 2/3 + κ_s/2, not 7/12 + κ_s/2. It is < ¾ exactly when κ_s < 1/6, the condition already stated. The line now carries 2/3 and the arithmetic. |
| m2 | #3.96-1-1 | The polydisc of §4(c) is centred at V′^X₀. On the support of χ̄, ∣V′ − 1∣ < (1 + κ_s)M₀ε_k ≤ ε₁/8 (#4.152). Also ∣V′^X₀ − 1∣ < C_X(M)ε_k ≤ ε₁/4 (#4.50, #4.51-1). So Y := (1/i)log(V′(V′^X₀)^{−1}) has ‖Y‖_∞ ≤ (π/2)(3ε₁/8) < ε₁ < 2C₁ε₁. The line was split from #3.96-1. |
| m3 | #3.99 | B_LF is a supremum over the large-field terms, which carry the soft tests, so its bound holds with them by (R-s)(b) (#3.45). Only e^{C_Σ𝔞̄} reads no test. |
| m4 | #3.100 | LFR II (0.1), the lower bound with χ_k, is now classified with CRE (2.50) as a bound of the kind of (b). (1.104) alone carries tests in no comparison. #3.100 was split at CRE §2 into #3.100.1. |
| m5 | #3.100-1 | The list of the quotients' tests now includes the numerator's χ_k(Ω_k^{∼4}) (LFR I (1.100)), χ_k (LFR II (1.1)), and 𝕋″_k, which do not depend on V_k⌈_Λ (#3.80-2). The line now says it summarises the page checks #3.49–#3.99. |
| m6 | #3.85, #3.86-1-1 | The determining set is local, with support in □^{∼4} (CRE p.256 l.58–59). So its scale-0 layer is □^{∼4} ∖ Ω_1, not every bond outside Ω_1. REG (1.65) holds under REG (1.33)–(1.35) (p.82, p.87). Its (1.34) is the axial gauge Ax_k(𝔅_k, U_{k,Z}), unique in each orbit of REG's subgroup (1.14) by (1.19) (p.79). The representative in that gauge is exp(iη𝐇_{k,□}(B))U_{k,Z} = U_{k,□}^u of #3.85-1, before u^{−1}. |
| m7 | #3.76 | LR_{h+1} ≥ R_h now cites CRE (2.5)–(2.6). |
| m8 | #3.94, #3.94-1, #3.96-1-1, #3.82-1–#3.82-2 | Each part is repaired as follows. |

The parts of m8:
- **#3.94's constant.** The generic constant is now C_den(M) := O(1)(1 + log M)M⁴, stated not to be §4(c)'s C(M). It collects the linear term, V, σ, and d(1)'s O(1)log M∣Λ∣ with ∣Λ∣ ≤ O(M⁴).
- **#3.96-1-1's C₁.** The line names #4.50's C₁ and separates it from CRE (2.28)'s C₁ of #3.70.
- **#3.94's wording.** It now reads "by (1.7)–(1.9), whose bounds p.358 l.27–33 extends to the complex backgrounds of the class".
- **#3.82's blanket statement.** #3.82-1–#3.82-2 list the places on LFR II pp.356–377 where a passed test enters, each through the regularity ε_k of the background. I located them in the transcription, LFR2\parts p356–p377, by every ε_k and α_{0,k} on those pages. They are:
  - p.357: 3ε_k∣Λ∣ and O(1)M⁶R_kε_k;
  - p.358: the form's lower bound and its complex extension;
  - p.359: the contraction constant;
  - pp.360 and 365: 44d²ε_k;
  - p.361: O(1)B₃²B₅M⁵ε_k;
  - p.362: 11d²ε_h;
  - p.363: two bounds;
  - p.366: the quadratic bound;
  - p.367: 𝐇_{k,Λ} at α's;
  - p.368: one bound.

  Each is linear in ε_k, or quadratic at p.366, with an O(1) constant. So 1 + 2κ_s, or (1 + 2κ_s)², multiplies that constant.

## The Renames

The user confirmed the renames of the duplicate definitions on 6 Nov 2026. The appendix's δ_H became δ_red, its S_j became S^{in}_j, and its μ₀ became μ_J. #4.206's ψ_f became ψ_J. #4.120 no longer redefines b_w(W) and cites #4.41. The Cauchy note's b_w became b^{wr}. The LF now has no D-tag that appears twice.

## Pre-check for r3

I re-read every changed line and re-derived the arithmetic of m1 and m2. The LF's one other 7/12 is ½ + α at α = 1/12, from (1.95) without the factor 2, and is correct. No line of the part uses the unqualified C(M) of #3.94, or the old classification of (0.1).

Second pass (6 Nov, 21:23), after 12a closed. I read the whole part #3.63–#3.100-1 again. Against the r2 packet, the changed tags are #3.76, #3.77, #3.82-1, #3.82-2, #3.84, #3.84-1, #3.85, #3.86-1, #3.86-1-1, #3.91, #3.94, #3.94-1, #3.96, #3.96-1, #3.96-1-1, #3.99, #3.100, #3.100.1, and #3.100-1.
- **#3.86-1, a weak point, repaired.** It applied REG (1.65) "with α₁ = 0", but REG (1.35) is a strict bound and fails at α₁ = 0. CRE p.266 l.12–13 itself uses "the reasoning leading to that inequality". The line now applies that reasoning (REG p.87 l.36–40, Lemma 1 iterated down from the equal k-block averages). With α₁ arbitrary and positive, it gives ≤ 11d²α₀, so abs(B) ≤ (π/2)11d²α₀ < 18d²α₀, and #3.87's τ is unchanged. #3.86-1-1 now says "That reasoning holds under REG (1.33)–(1.35)".
- **#3.84 and #3.76 now agree.** #3.84 had (L + 4)M₂R_k where #3.76 has (dL + 4)M₂R_h. It now reads (dL + 4)M₂R_k ≤ MR_k, as in #3.76. The line reached 634 characters, so it was split, with ∼ and the k-blocks moving to #3.84-1. #3.26-4 (in 12a, done) now cites #3.84-1 for the k-blocks, next to its "(#3.84)" (re-pointing).
- **Prints checked.** I re-read REG (1.14) (p.78), (1.19) (p.79 l.16: "determine uniquely an element in each orbit"), (1.33)–(1.35) (p.82), and (1.65) (p.87 l.36–44). I re-read CRE p.245 l.34–43, p.256 l.26–63, p.263 l.19–20, (2.50) (p.264), and (3.6)–(3.8) (p.266). I re-read LFR II (0.1) (p.355 l.31), p.358 l.20–35, and (1.104) (p.391 l.27–28). Each matches its citation.
- **Arithmetic re-derived.** #3.64: (1 + β/15)(1 − 7β/90) < 1. #3.77: 2/3 + κ_s/2 < ¾ for κ_s < 1/6. #3.78: κ_s < 1/44. #3.79: 29/12 + 2κ_s ≤ 21/8 for κ_s ≤ 5/48. #3.86-1: (π/2)11 < 18. #3.89: (1.25 + 0.1(1 + O(ε)))/(1 − O(ε)) < 2. #3.91: (π/2)M₀ε_k/2 < M₀ε_k. #3.96-1-1: (π/2)(3/8) < 1.
- **#T11.26.** The citations in #3.86-1, #3.91, #3.96, and #3.96-1-1 use CMP98 (24)–(25), which hold for every unitary.
- **Recheck before launch (user's go, 21:25).** The built packet lf-p12b-20261106-r3 was re-read line by line. χ̄'s ramp equals the average of sharp cutoffs of #3.92, t = M₀p₀(g_k) = M₀ε_k/g_k (#T3.27), and LFR II p.378 l.10–14 matches #3.86, #3.91, and #3.96. Nothing new was found.
- **Size and pin.** The packet is 19.0k (r2: 18.1k). It is pinned to LF 2cf459f08800 (labels bdd692ad0d20), table 1e392e405632, with 0 definition conflicts. It is built but not launched; the launch waits for the user's go.

## Files

r2: LF f4cbd0993021. After the repairs and renames: LF 0cb0774db832, labels 2cae8138d3d9, table a8041051efc3, Cauchy note 7b77257e745a. 12a r4 launches next. 12b r3 and p13 r1 follow, one at a time.
