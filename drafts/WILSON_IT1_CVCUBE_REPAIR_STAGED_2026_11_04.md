# Open (CV-cube): Staged Repair of #130.15.2 (5)

Staged during CV13; apply to the two-loops note after CV13 lands. Status: derived, not reviewed.

## Replace in #130.15.2 (5)

Old, from "Each Ω_m made by a renormalization transformation" to "**Open (CV-cube)**. Where □ exists (n_j = n, or Ω_n made by a renormalization transformation), □ has size", by the text below, which ends with "□ has size".

New:

Every Ω_m is a union of MR_m-cubes of the scale m, from mutually compatible partitions, where R_m is a power of L with R_m ≥ (log g_m^{−2})^r > 1 for g small (CRE (2.5), p.255 l.36–38), so R_m ≥ L. A domain made by a renormalization transformation is such a union (CRE p.256 l.21–22; p.257 l.28, l.42–43). An R-operation at the step i keeps this. Its admissible sequences of M-cubes (LFR I (1.10), p.179 l.19–24) lie inside its region Z and belong to the intermediate layering 𝐁″_i. The post-R layering, on which 𝒟^λ_i is posed, puts all of Z on the layer i (LFR II (1.33), p.365 l.2–7), and on Z^c it is the layering before the operation (LFR I (1.12), p.179 l.35–36). So the post-R domains are Ω_m ∪ Z for m ≤ i. Z is a union of components of Λ_i^c (LFR I p.177 l.17, l.33), and Λ_i is a union of MR_i-cubes of the scale i. So Z is a union of MR_i-cubes, and so of MR_m-cubes of the scale m for every m ≤ i, since the side ratio L^{i−m}R_i/R_m is a power of L and at least 1 and the partitions are compatible. The distance from Ω_{n+1}^c to Ω_{n+2} is at least ML^{n+1}ξ = La ≥ 8a:
- A renormalization transformation at the step m + 1 builds Ω_{m+1} outside (B^{m+1}(P^1_{m+1})^c)^{∼3} (CRE (3.5), p.265 l.43), with B^{m+1}(P^1_{m+1}) ⊂ (Z_m′^{∼5})^c (p.265 l.18–19), and Z_m′ ⊇ Z_m = Λ_m^c ⊇ Ω_m^c (p.264 l.52–53). So Ω_{m+1} is at least eight layers of MR_{m+1}-cubes of the scale m + 1 from Ω_m^c, whether or not an R-operation has made Λ_m = Ω_m (CRE p.255 l.1–3). Eight such layers are ≥ 8R_{m+1}ML^{m+1}ξ ≥ ML^{m+1}ξ.
- An R-operation at the step i ≥ n + 2 adds Z to Ω_{n+1} and to Ω_{n+2}. A lattice neighbour of Z outside Z lies in Λ_i ⊂ Ω_i ⊂ Ω_{n+2}, since Z is a union of components of Λ_i^c. Let p ∈ Z and q ∉ Ω_{n+1} ∪ Z. A monotone nearest-neighbour path from p to q leaves Z at a point r ∈ Ω_{n+2}, and each coordinate of r lies between those of p and q. So |p − q| ≥ |r − q| ≥ dist(Ω_{n+1}^c, Ω_{n+2}) before the operation. At i = n + 1 the operation adds Z to Ω_{n+1} only, which does not decrease the distance. So the distance holds after every R-operation, by induction over the steps.

If n_j = n, put □ := □′. If n_j < n, the side of □′ is CML^{n_j}ξ ≤ 2a/L. Every MR_n-cube of the partition that meets □′ lies in Ω_n, since it contains a point of □′ ⊂ Ω_n and Ω_n is a union of such cubes. These cubes form a box with sides at least R_na ≥ 2a that contains □′, and □ is a cube of size Ca in that box containing □′. □ has size

## Also

- #130.15.2's heading: "(derived, not reviewed, apart from (5)'s Open (CV-cube))" → "(derived, not reviewed)".
- Remove the Open (CV-cube) marks at #3, #6, #130.15.1, #60, #61, #63, #68, and every other "apart from Open (CV-cube)" (grep), and at the scopes' declared opens.
- Before applying: re-read #130.15.2 (5) as it stands after CV13, and check the pins above against the corrected files (done once: LFR I p.177 l.17, l.33; p.179 l.19–24, l.35–36; LFR II p.365 l.2–7; CRE p.255 l.1–3, p.256 l.21–22, p.257 l.28, l.42–43, p.264 l.52–53, p.265 l.18–19, l.43).
