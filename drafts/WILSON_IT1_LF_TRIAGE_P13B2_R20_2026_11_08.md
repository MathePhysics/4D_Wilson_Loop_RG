# Triage of lf-p13b2-20261108-r20

## Verdict

- r20 was a narrow round of 13b2 on r19's repairs, at LF 179f5fa14433, table 6d09b1b5054d, and labels 971e7d7d5325.
- **Fatal:** none. **Serious:** none.
- **Minor:** m1′. r19's m1 repair made d_y weighted and claimed the weighted bound is abs(w)_y times the unweighted one. That holds for the alignment piece. It fails for the blocking artefact b_y, which then carries #4.41-3's weight-difference term.
- **Trivial:** t-a, t-b, t-c.
- r19's t1–t5 were confirmed repaired, with t2 and t5 refined by t-b and t-a.
- The round is **not clean**, so 13b2's count stays 0. The next round, r21, is narrow, then a full round.

## Repairs

| Finding | Line | Issue | Repair |
|---|---|---|---|
| m1′ | #4.565, #4.565-0, #4.565-1 | The weighted b_y has the term Σ_pΣ_{p′ ∈ cell(p)}(w(p) − w(p′))t(U^B, p′), which #4.41-3 bounds separately; "the weighted one is abs(w)_y times it" is false for it | Repaired at the root, by the referee's r19 alternative: (c)'s d_y is unweighted, as Φ = A(U) is (#4.44). #4.565: "unweighted, as Φ is (#4.44), are ≤ C_y(M)g_{j(x)}^{−2}(…)ε₁′² (#4.565-0), the factor g_{j(x)}^{−2} ≥ 1 being slack"; #4.565-0: "the bound C_y(M)(…)ε₁′², …, and g_{j(x)} ≤ (1 + β₀)ḡ ≤ 1 for ḡ small (#4.41-1-1)"; #4.565-1: #4.563-3's per-run bound is "a bound of the unweighted density too, since the weight (g″)^{−2}, between the layer values g_j^{−2} (#4.41-1-1), is ≥ 1", and C_dc(M) := max(C_y(M), 2C_act) |
| t-a | #4.517-0 | X and Y of "Y ↦ XYX^{−1}" overload {#D.X} and {#D.Y} | "each conjugated by a transport of the real base U₀" (no symbols) |
| t-b | #4.561.1-1 | The continuity argument for B^e ∈ 𝔤^c stated only the base case | The statement moves to the new #4.561.1-1-0, with the openness step: at t₀ with X₀ ∈ 𝔤^c, abs(X₀) ≤ ¼, W(t₀z)^{−1}W(tz) = e^Z with Z ∈ 𝔤^c small; the BCH series of (X₀, Z) is a 𝔤^c logarithm of norm < log 2, hence the principal one, since exp is injective there; so the set is open and closed and contains 0 |
| t-c | #4.563-3-1 | "(g″)^{−2} ≤ 2g_{j(x)}^{−2}" needs 2b₂ḡ² ≤ 1 | "(g″)^{−2} ≤ (1 + 2b₂ḡ²)g_{j(x)}^{−2} ≤ 2g_{j(x)}^{−2} (#4.41-1-1, 2b₂ḡ² ≤ 1 for ḡ small)" |

## Checks

- **m1′, the object.**
  - (c)'s comparison adds the two growth inequalities of Φ = A(U_{k,Z}(·)) (#4.44, #4.51), with no coupling. d_y (#4.51-0) is the per-block piece of δΦ = Φ^A − Φ^B, built from a_y, the unweighted plaquette sums (#4.48).
  - The class version bounds the same d_y. #4.48.0 and #4.51-1.0 give C_y(M)(ε/a_n)^{(1−ε₀)/3}ε₁′², unweighted, which is r19's referee's verdict on #4.565-0.
  - g_{j(x)}^{−2} ≥ 1 since g_{j(x)} ≤ (1 + β₀)ḡ (#4.41-1-1) and ḡ is small.
- **m1′, the disc.**
  - On the disc, abs(d_y) ≤ the sum of the two runs' unweighted densities.
  - Each of these is ≤ ½d(d − 1)(c_plC₀^{ms}ε₁′)² ≤ C_actg_{j(x)}^{−2}ε₁′² (#4.563-3-1 without the weight), since (g″)^{−2} ≥ 1 makes the weighted per-run bound an upper bound of the unweighted one.
- **m1′, the Lemma.** At z = i with 𝔨 = C_y(M)g^{−2}(ε/a_n)^{(1−ε₀)/3}ε₁′² and 𝔎 = 2C_actg^{−2}ε₁′², 𝔨^{15/16}𝔎^{1/16} ≤ max(C_y(M), 2C_act)g^{−2}(ε/a_n)^{5(1−ε₀)/16}ε₁′². This is the value of table row 466, which therefore needs no change; the C_dc change sent to the fork at 10:02 is withdrawn.
- **m1′, consumers.**
  - #4.568 uses C_dc(M) by name and the form g^{−2}ε₁′², unchanged.
  - #4.567 bounds the coupling terms by the weight difference times the disc bound of a density, consistent with unweighted densities.
- **t-b.**
  - abs(X₀) ≤ 2c_avε′_k ≤ ¼ by c_avε′_k ≤ ⅛ (#4.561.1-0).
  - BCH converges for abs(X₀) + abs(Z) < log 2.
  - If e^X = e^Y with abs(X), abs(Y) < log 2, then abs(e^X − 1) < 1 and the principal logarithm returns both, so X = Y.
  - Closedness holds since t ↦ log W(tz) is continuous and 𝔤^c is closed.
- **Symbols.** #4.561.1-1-0 was checked unused before creation. C_y(M) and C_dc(M) occur only at #4.565–#4.565-1 and #4.568. The weighted constant proposed by the referee was not introduced.
- **Line lengths.** #4.517-0 567, #4.561.1-1 375, #4.561.1-1-0 478, #4.563-3-1 498, #4.565 555, #4.565-0 335, #4.565-1 414 characters. CR count 0.

## Pre-check of lf-p13b2-20261108-r21 (narrow)

- **Spec.** specs\spec_p13b2_r21.json, prior r20, extracts as in r20.
- **Named steps.** The changed lines #4.517-0, #4.561.1-1, #4.561.1-1-0, #4.563-3-1, #4.565, #4.565-0 and #4.565-1, with their consumers #4.561.1-1.1, #4.567 and #4.568.
- **Changed since r20.** The seven named lines above. Every one was re-read in place after the edit.
- **Cited lines re-read:** #4.41-1-1 (g_{j(x)} ≤ (1 + β₀)ḡ, (g″)^{−2} between the layer values), #4.41-3 (b_w's weight-difference term, now not entered), #4.44 (Φ := A(U_{k,Z}(V′V_{Λ^c}))), #4.51-0, #4.563-3–#4.563-3-1.
- **Size.** Built at LF 6ce650aff3e6: argument 24,909 characters (r20: 24,554), 28 files, within 25k. The growth is the openness step of t-b. A further round that grows the part must split it first.
- No known weak point and no OPEN is in the part.

## SHAs

LF 179f5fa14433 (r20's snapshot) → 87e0431cfd68 (12b's #3.70-5-1, outside this part) → 6ce650aff3e6 (m1′, t-a–t-c). Table 6d09b1b5054d and labels 971e7d7d5325 (unchanged; relabel and rows pending with the table fork).
