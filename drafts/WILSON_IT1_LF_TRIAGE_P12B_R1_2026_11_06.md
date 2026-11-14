# Packet 12b r1 Triage (LF #3.63–#3.100-1)

## The Run

r1 (lf-p12b-20261106-r1) was launched under .claude-Main while 12a r2 was running, against the rule "one referee of one's own at a time". Neither run was stopped, and the breach is logged in SESSION_HANDOVER.md (16:22).

## The Report of r1

r1 found no fatal finding, no serious finding, and thirteen minor ones. So r1 is not clean, and r2 is a full round. Each finding was re-derived against the print and repaired in place.

| Finding | Item | Repair |
|---|---|---|
| 1 | #3.64 | The cascade input carries (1 + κ_c)^{N−n+1} ≤ 1 + 2κ_s. The margin is now (1 + 2κ_s)(1 − β/10 + β/(5L²)) ≤ (1 + β/15)(1 − 7β/90) < 1, with the boundary-layer term 22d²ε_j of p.184 l.3–4. |
| 2 | #3.77 | The full expression of (1.91) is used, [½(1 + κ_s)(1 + L^{−h}αε_h)² + (α + 8α²ε_h)(2 + L^{−h}αε_h)]ε_h(L^{k−h}η)². At α = 1/12 (p.199 l.16) this is (7/12 + κ_s/2 + O(ε_h)) < ¾, for κ_s < 1/6 and γ small depending on 1/6 − κ_s. |
| 3 | #3.68-1 | The slack is now bounded above, ≤ ℓβxε_i(L^{k−i}η)²/4 ≤ βxT_n(p)/(4(1 − β)), with x := 2^{−(j−i)} and ℓ := L₀^{2max{0,i−k₀−1}}. |
| 4 | #3.68-3 | a and y come from the field (1/i)log[V_j(V_Z^{(j)})^{−1}], bounded by the soft (1.27) only (p.186 l.8–9, (1.44)–(1.45)). |
| 5 | claim (b) | The spec of r2 states ∣log d̄ − log d(1)∣ ≤ ½, as #3.95 does; the second τ is gone. |
| 6 | #3.86 | Rewritten. The plaquettes are below O(1)B₃(1 + κ_s)ε_kη², from p.378 l.10–11 with the soft χ_k of width κ_s and VAR Theorem 1 ((8), p.279) at ε₁ = 2(1 + κ_s)ε_k. REG (1.65) gives ∣M^·(U_{k,□}) − M^·(U_{k,Z})∣ < 11d²α₀, and the logarithm bound ∣(1/i)log v∣ ≤ (π/2)∣v − 1∣ gives ∣B∣ < 18d²α₀ (#3.86-1). τ (#3.87), #3.89, and #3.90 carry 1 + κ_s. |
| 7 | #3.85 | Derived from the structure of the localised determining set (CRE p.256 l.57–63 with (2.2), p.255 l.15). Its scale-0 layer contains the bonds outside Ω₁, where its data are U_{k,Z}, and its L^n-block averages iterate to the k-block averages of 𝔹_k(Z). So a competitor extended by U_{k,Z} is admissible for the Z-problem with the same change of the action, and U_{k,Z} is the local minimiser at its own data by the uniqueness of the minimal orbit (#3.85-1). |
| 8 | #3.91 | The comparison now goes through ∣(1/i)log V′_k(b)∣ ≤ (π/2)∣V′_k(b) − 1∣ < M₀ε_k. |
| 9 | #3.96 | M₀ := 2(1 + κ_s)O(1)B₅M⁶, the factor 2 covering the logarithm. "Enters only" is replaced by the list of places where M₀ enters (#3.96-1). The order condition is discharged: the support of χ̄ lies in the polydisc, since (1 + κ_s)M₀ε_k ≤ ε₁/8 < 2C₁ε₁ by C(M) ≥ 8(1 + κ_s)M₀ (#4.152) and C₁ ≥ 1 (#4.50). |
| 10 | #3.98, #3.100 | The printed (1.102) (p.390 l.37) omits χ(Λ_i), which (1.72) (p.379 l.17) and (1.104) (p.391 l.27) carry, so 𝐓_k carries the soft χ̄(Λ_i). The coverage adds LFR II (0.1) (p.355 l.31) and (1.104) (p.391 l.27–28), which carry tests in no comparison. |
| 11 | #3.99, #3.47 | Rewritten. B_W of the continuum note's (8.1) reads the tests through B₃ε_{K′} in its (5.3) and (5.5); with the soft tests ε_{K′} is enlarged by 1 + 2κ_s, so 8.48 and the O(1) of O(C_χρ_{K′}) are multiplied by 1 + 2κ_s. #3.47 now says that B_W holds with this factor. |
| 12 | #3.76 | Derived, no longer read. The cubes of χ_h(Ω_h ∩ Z_h) lie with □^{∼4} within LMR_{h+1} of Z_h. By CRE (3.2)–(3.5), Ω_{h+1} ⊂ (Z′^{∼8}_h)^c, so Ω″^{∼2}_{h+1} ⊂ Ω^{∼7}_{h+1} misses □^{∼4}. Then (1, V_h) = V_h on the bonds that U_{h,□} reads (CRE (2.16); p.246 l.46), and the passed soft χ_{h,1/2} gives < ½(1 + κ_s)ε_h(L^{k−h}η)², below the threshold of (1.3) (#3.76-1). |
| 13 | #3.80 | "The quotient stays an identity" is replaced by "the factor that (1.100) inserts still integrates to 1, which is (1.102)". |

From the per-step verdicts, at the same time:

- **#3.78.** 22d²(1 + 2κ_s)ε_h + 2δ′_k < 23d²ε_h for κ_s < 1/44 and γ small.
- **#3.73.** The soft χ_{h,1/2} is 1 on the cubes inside Ω″^{∼2}_{h+1} and not touching its boundary (p.198 l.4–8).
- **#3.84.** Both inputs have width κ_s, < (1 + κ_s)ε_kη².

All transcript pins were re-checked by grep against the corrected files (l.N = line N of the file).

## Pre-check for r2

I read every line of #3.63–#3.100-1 as they now stand and re-derived the arithmetic:

- 2κ_s = β/15, and β/10 − β/45 = 7β/90 at L = 3 (#3.64).
- 1 + ¼ + (1/10)(1 + 4τε_k) < 2 at κ_s ≤ ¼ and τ ≤ 1/20 (#3.89).
- ∣log z∣ ≤ (1/4)/(3/4) = 1/3 ≤ ½ for ∣z − 1∣ ≤ ¼ (#3.95).
- (1 + κ_s)M₀ε_k ≤ ε₁/8 from C(M) ≥ 8(1 + κ_s)M₀ and R_k ≥ 1 (#3.96-1). #4.152 states this condition and #4.50 defines C₁ ≥ 1.

The lines #3.76, #3.84, #3.85, #3.86, and #3.96 exceeded ~600 characters.

- The tails of #3.85 and #3.96 moved into their existing children #3.85-1 and #3.96-1.
- #3.86 was split into #3.86-1.
- #3.76 dropped a duplicated gloss of p.245 l.37–38.
- The citations "the argument of #3.85" (#0.1.9, #0.1.41) now read #3.85–#3.85-1.

The definition check passed for spec_p12b_r2.json: 0 conflicts, 4 allowed (B, W, X, t).

## Files

r1: LF fc510e5cad00. r2: LF ad44c62ee742, labels 2bcd7b0b486a, table 88a6dcbd277a; Cauchy note 9250f39dd504. r2 launches after 12a r3 has reported and been triaged.
