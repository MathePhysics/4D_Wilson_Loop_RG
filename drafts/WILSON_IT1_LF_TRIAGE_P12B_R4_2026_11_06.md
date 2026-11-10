# LF packet 12b, round 4 (full): triage

Review: verification/isolated_reviewer/reviews/lf-p12b-20261106-r4/review.md. Under review: LF a4a5e1332d54 (labels 644901ba13c6), table 1e392e405632.

## Verdict

No fatal or serious finding. There is one minor finding and four trivia, so r4 is not clean. All r3 findings are repaired. Every r4 finding was checked against the print and repaired in place.

## Repairs

- **Minor (#3.86-1-1).** The line called exp(iη𝐇_{k,□}(B))U_{k,Z} the axial representative that carries the data. That is reversed. 𝐇 is the Landau-gauge function: REG (1.36)–(1.38) has U₁ = e^{iηA} with R(U₀)D*_{U₀}A = 0, and CRE p.251 l.35 says (190) is "formulated … for the Landau gauge". REG p.81 l.24–25 states that the Landau image "is not contained in 𝔙_k(𝔅_k, V)", so it does not carry the data. The line now reads M^·(U_{k,□}) and B at the representative of U_{k,□} = (exp(iη𝐇_{k,□}(B))U_{k,Z})^{u^{−1}} that carries the data (REG (1.28)). The new line #3.86-1-2 states that exp(iη𝐇_{k,□}(B))U_{k,Z} is its Landau-gauge representative, which enters only through gauge-covariant plaquettes (#3.88). No bound changes, since B depends only on the data. The line reached 669 characters and was split at the sentence boundary.
- **Trivia.**
  - #3.69: "at CRE p.269 below" now reads "above (#3.61)".
  - #3.94-1: C_den(M)'s list now includes the Gaussian normalisation (8π/κ_Λ)^{O(|Λ|)} of e^{−(κ_Λ/8)‖B′‖²}, which is within O(1)(1 + log M)M⁴ since |Λ| ≤ O(M⁴).
  - #3.63, #3.81, and #3.100: the section ranges are now LFR I §1 (pp.177–202) and LFR II §1 (pp.356–392). The section headings are at LFR I p.177 l.12 and LFR II p.356 l.8, and the References begin at LFR I p.202 l.8 and LFR II p.392 l.12.
  - #3.82-1: p.363's entry now carries the printed prefactor, (d − 1)L^{−h}O(1)B₃B₅M⁵ε_kη² (p.363 l.32).
  - #3.79: the absorption is now cited at p.200 l.23–36, matching "≤ 1/4 for R_k^{−α₀}, or γ sufficiently small" at l.35–36.

## Why the r4 minor was not caught before r4

The recheck before r4 re-read only the lines changed since r3. The line-by-line read before r3 checked that each REG equation cited in #3.86-1-1 exists and says what it is cited for. It did not test the one sentence without a citation, which identified exp(iη𝐇)U_{k,Z} as the axial representative. Checking it needed REG (1.36)–(1.38) and CRE p.251 l.35, which were not opened. So the recheck verified the citations, not the claims that had none.

## Claim-by-claim recheck (22:20)

I checked every claim of #3.63–#3.100-1 that carries no pin, or an indirect one, against the print.
- **#3.80-2.** "dist(Ω_k, Λ) is large (LFR II (1.6))" was an indirect second reason; (1.6) uses the distance but does not state it. The line now gives the direct reason. χ_k(Ω_k^{∼4}), 𝕋″_k, and exp A″_k are factors of (1.99) (LFR I p.200 l.53–p.201 l.5), the expression obtained by the integration over V_k⌈_Λ, which is "independent of V_k⌈_Λ" (p.194 l.2–3).
- **#3.70.** "Bałaban's spaces contain his supports … with no condition on q₀ and q₁ beyond (2.28)" was a reading with no print. p.190 l.7–37 prints the spaces as (1.24)'s bounds with ε_m replaced by α_{0,m}. Containment therefore needs α_{0,m}/ε_m = (C₀/A₀)(log g_m^{−2})^{q₀−p₀} ≥ 1 + 2κ_s, which holds for γ small because q₀ > p₀ (#T1.2; LF #0.10). The line now states this; the false "no condition on q₀" is gone.
- **#3.84.** "□ lies in Ω_k^{∼4} or in (Ω_k^{∼4})^c ∩ X_i" now cites the compatibility of the partitions (CRE p.245 l.38–40).
- **Checked and unchanged.**
  - CRE §1 (pp.245–254), §2 (pp.254–264), and §3 (pp.264–285), against the section headings at p.245 l.24, p.254 l.33, p.264 l.37, and p.285 l.8.
  - #3.92's y = |B′|/t (p.356 l.37; #T3.27).
  - #3.83's real configurations.
  - #3.87's distance.
  - #3.88's W as the Landau representative.
  - Every remaining claim carries a pin that r3 or r4 checked.

## Pre-check for lf-p12b-20261106-r5

- **Changed tags:** #3.63, #3.69, #3.70, #3.79, #3.80-2, #3.81, #3.84, #3.86-1-1, #3.86-1-2, #3.94-1, #3.100, and the p.363 entry of #3.82-1. #3.70 is 583 characters, #3.80-2 273, and #3.84 444.
- **Each line re-read.** #3.69 is 431 characters, #3.79 464, #3.86-1-1 432, #3.86-1-2 248, #3.94-1 586, and #3.100 348.
- **Prints checked.** REG p.81 l.1–30, (1.36)–(1.38) (p.82 l.48–58), and Theorem 2 (p.83 l.18–20: U₁ = U′^{u^{−1}}). CRE p.251 l.30–38. LFR I p.177 l.12, p.200 l.22–36, and p.202 l.8. LFR II p.356 l.8, p.363 l.25–32, and p.392 l.12.
- **Consumers.** Only the spec claim cited #3.86-1-1; it is updated to #3.86–#3.86-1-2. No line still cites "pp.178–201" or "pp.356–390". #3.88's W, with U₁ = exp(iη𝐇), is the Landau representative, consistent with the repair, and |W − 1| = |U_{k,□}(∂p) − 1| by gauge covariance.
- **Size.** The packet is 19.8k (r4: 19.3k). There are 0 definition conflicts.
- **Pins.** LF d523fd2a521f (labels cbec9b3be3ca), table 1e392e405632, Cauchy 4138f0908f6d. The packet was rebuilt after the claim-by-claim recheck; the first build was never launched.
- **Status.** Built; awaiting the user's go.
