# Bałaban Proof: The Rate of CRE's Pinned Expansion

CRE (3.44)–(3.47) (p.277 l.31–p.278 l.31) write the expectation value of a localised observable, pinned at a bond b, as a sum of terms 𝐄₀(Λ_{k+1}, X, b) over X ∋ b, and p.278 l.32–33 bounds them by (2.42) with B₀ replaced by O(p₀³(g_k)), at the rate κ. #PE.1 derives the rate (1 − 10δ)½Lκ − η₀ from RG2's bounds; RC_PROOF_PASS_2026_10_23.md #RC.4-4-2 uses it for the improved decay of newly created terms (CRE p.262 l.24–29). CRE = CMP 122 and RG2 = CMP 116; pins are to Balaban\tex\<paper>\parts\pNNN_corrected.tex, and (I.7.x) is RG2's (2.x).

## Statement

- {#PE.1} *Statement.* Write 𝔞_H := (1 − 8δ)½Lκ and 𝔞_E := (1 − 10δ)½Lκ, the rates of RG2 (2.38) and (2.41), and let η₀ := 2⁹(6 log 2 + 1) and K_𝐃 := 2^{6·2¹⁰} + 1 be the constants of #BK.5-1. Assume:
  {#PE.1-1} (i) the factor H′(Z₀) of (3.44), for the domains Z₀ ∈ 𝐃_{k+1} containing b, satisfies |H′(Z₀)| ≤ B′e^{−𝔞_Hd_{k+1}(Z₀)}, B′ the constant of the observable (CRE p.277 l.44–p.278 l.1: "it satisfies the same bound as the other factors", the bound (2.38));
  {#PE.1-2} (ii) for each such Z₀ the exponents 𝐄̃(Λ_{k+1}, Y) of (3.46) satisfy |𝐄̃(Λ_{k+1}, Y)| ≤ c_cle^{−𝔞_Ed_{k+1}(Y)}, c_cl := O(1)C₃ε₁ ≤ ½ with (2.41)'s O(1): each is a sum over the clusters (Z₁, …, Z_n) with ∪Z_i = Y and some Z_i meeting Z₀ along a wall (p.278 l.6–10), a part of the absolutely convergent sum that (2.39)–(2.41) bound;
  {#PE.1-3} (iii) 𝔞_E ≥ η₀, δLκ ≥ 1, and c_Σ := 9·2¹⁰c_cle^{5𝔞_E}K_𝐃 ≤ 1 (ε₁ small after κ and L, RG2 p.21 l.11).
  {#PE.1-4} Put 𝔞_P := 𝔞_E − η₀ and 𝐄₀(Λ_{k+1}, X, b) := Σ_{Z₀∋b}H′(Z₀)Σ_{𝒴′}Π_{Y∈𝒴′}(e^{−𝐄̃(Λ_{k+1},Y)} − 1), the inner sum over the finite sets 𝒴′ of domains Y of (3.46) with Z₀ ∪ ∪𝒴′ = X: the Mayer expansion of (3.46)'s exponential, resummed by X (p.278 l.13–15). Then |𝐄₀(Λ_{k+1}, X, b)| ≤ 2⁶K_𝐃B′e^{−𝔞_Pd_{k+1}(X)} for every X ∋ b.

## Proof

- {#PE.2} *One term.* Fix Z₀ and 𝒴′ with Z₀ ∪ ∪𝒴′ = X. Each Y ∈ 𝒴′ has a cube equal to, or sharing a wall with, a cube of Z₀; a segment between points of these two cubes lies in their union and has length at most 5M in every norm |·|_p. So shortest trees of the members, joined by such segments, give (2.27) for the family {Z₀} ∪ 𝒴′ (RG2 p.18 l.4–7): d_{k+1}(X) ≤ d_{k+1}(Z₀) + Σ_{Y∈𝒴′}(d_{k+1}(Y) + 5), and X is connected.
  {#PE.2-1} As |e^{−u} − 1| ≤ |u|e^{|u|} ≤ 2|u| for |u| ≤ ½, and 𝔞_H = 𝔞_P + δLκ + η₀, 𝔞_E = 𝔞_P + η₀ with 𝔞_P ≥ 0, the term is at most B′e^{−𝔞_Hd_{k+1}(Z₀)}Π_{Y∈𝒴′}2c_cle^{−𝔞_Ed_{k+1}(Y)} ≤ B′e^{−𝔞_Pd_{k+1}(X)}e^{−(δLκ+η₀)d_{k+1}(Z₀)}Π_{Y∈𝒴′}u_Y, u_Y := 2c_cle^{5𝔞_P}e^{−η₀d_{k+1}(Y)}, by #PE.2's inequality.
- {#PE.3} *The sum over 𝒴′.* Dropping the condition on the union, Σ_{𝒴′}Π_{Y∈𝒴′}u_Y ≤ Π_{Y∈𝒴(Z₀)}(1 + u_Y) ≤ exp Σ_{Y∈𝒴(Z₀)}u_Y, 𝒴(Z₀) the finite set of domains of (3.46) for Z₀. Each contains one of the at most 9#cubes(Z₀) cubes that equal or share a wall with a cube of Z₀ (d = 4), and Σ_{Y∋□}e^{−η₀d_{k+1}(Y)} ≤ K_𝐃 (#BK.5-1 with η₀ for κ). With #cubes(Z₀) ≤ 2⁹(1 + d_{k+1}(Z₀)) (#BK.1-1) and 𝔞_P ≤ 𝔞_E, Σ_{Y∈𝒴(Z₀)}u_Y ≤ 9·2⁹(1 + d_{k+1}(Z₀))·2c_cle^{5𝔞_P}K_𝐃 ≤ c_Σ(1 + d_{k+1}(Z₀)).
- {#PE.4} *The sum over Z₀.* A bond b lies in at most 2⁴ cubes of π_{k+1}, and a Z₀ ∋ b contains one of them. By #PE.2–#PE.3 and (iii), the terms with domain X sum to at most B′e^{−𝔞_Pd_{k+1}(X)}Σ_{Z₀∋b}e^{c_Σ}e^{−(δLκ + η₀ − c_Σ)d_{k+1}(Z₀)} ≤ eB′e^{−𝔞_Pd_{k+1}(X)}Σ_{□∋b}Σ_{Z₀⊃□}e^{−η₀d_{k+1}(Z₀)} ≤ 2⁴eK_𝐃B′e^{−𝔞_Pd_{k+1}(X)} ≤ 2⁶K_𝐃B′e^{−𝔞_Pd_{k+1}(X)} (#BK.5-1 again). ∎
