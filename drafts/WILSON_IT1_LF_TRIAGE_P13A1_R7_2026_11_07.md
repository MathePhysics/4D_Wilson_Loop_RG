# Triage: LF part 13a1, round 7 (lf-p13a1-20261107-r7), 7 Nov 2026

## Verdict

Clean: no fatal, serious, or minor finding. There are three trivial remarks (r1–r3). This round was a full round, and round 6 was clean and full. **Part 13a1 is done.**

LF reviewed at 11ce11342b9a (table d8006ecd710f, LABELS a44bb969f4f4). The repaired LF is ad6909e8de2e. The relabel and the #T12.9 row were requested from the table fork.

The referee confirmed the round-6 repairs t1–t5. It found no misquotation, no volume or scale dependence, no circularity, and no SU(N)-specific fact.

## Repairs

| Finding | Where | Repair |
|---|---|---|
| r1: Δ carries four meanings in the part; Δ := ‖𝔛‖₂ is defined in #4.44-2 but first used in #4.51 | #4.44-2, #4.51 | The definition {#D.Δ} moves to #4.51, its first use. 13a1 keeps Δ₁, Δ(U_t), and Δ(y), each marked by its subscript or argument |
| r2: "at most eight of them per plaquette" in #4.48.0-2.1 is not exhibited | #4.48.0-2.1, #4.48.0 | {#D.n_tr} n_tr := the largest number of transports and inverses in a monomial of §9.6's coefficients (Cauchy #C9.6.1-4), a lattice count. The bound at U_t carries 2^{n_tr/8}C_hes^w, and C_bd := max(48L²C₀^{ms}, 2^{n_tr/8}C_hes^wL⁶) |
| r3 (observation): LFR I (1.83) is printed with ε_k, while (1.78) is at ε_P ∝ R_kε_k | none | No change. (1.83) is Bałaban's printed claim and is accepted. The referee checked that #4.50-0 also holds with R_kε_k, since C(M) ≥ C_𝔛(M) |

## Re-derivation of r2

At complex ℋ every transport of U_t and its inverse has operator norm ≤ e^{√N|ℋ|_y} ≤ 2^{1/8} (#4.48.0-2.1). So each monomial of §9.6's coefficients is at most 2^{n_tr/8} times its unitary bound. A crude per-bond bound of the plaquette Hessian would lose the gradient structure: it grows like (a_j/η)² per block. So the count must come from §9.6's form, whose coefficients are fixed polynomials. n_tr depends on neither k, the volume, C₁, nor M. Through C_bd it changes only the values of C_Φ, C_{1−ζ₀}, C₁, and the c in the thresholds cC₁ε₁ ≤ c′. The definitions of these constants are unchanged in form, and so are #4.50-1's dependence list and (T-Λ).

## Consumers

- C_bd: #4.48-1, #4.48-3.1, and #4.50-1.0 in 13a1, through the symbol only. #4.51-2.1 in 13a2 (2C_bd) also uses the symbol only. #T12.9 restates the definition, and the fork has been asked to change it.
- C_hes^w at real points (#4.41-3-3, #T4.35's C_w(ε₀)) is unchanged.
- Δ: it is used in #4.51, #4.51-2.1, #4.51-3, #4.53, #4.53-1.2, #4.55, and #4.154, all at or after #4.51. No line before #4.51 uses it.
- 13a2 r6 and 13b r3 are built at LF ff32ad403ddb, which has the #4.54-0 repair (22:08 relabel). The changes since then are in 13a2's background (13a1's lines), plus the bookkeeping move of Δ's definition into #4.51, so the snapshots stand. The next 13a2 round sees the move.

## Repaired SHAs

LF 11ce11342b9a → 7adee6408c88 → ad6909e8de2e. The second step adds ":=" to {#D.n_tr}, which labels_rebuild requires. The lines are 349 (#4.44-2), 359 (#4.48.0), 483 (#4.48.0-2.1), and 414 (#4.51) characters long.
