# Sphere packing upper bounds

Preprints and certificates for upper bounds on sphere packing density. Every bound covers all packings, lattice or not, periodic or not. These are upper bounds only. They do not prove that any packing is optimal.

## Layout

Each folder under [`preprints/`](preprints) holds one result: a `paper.pdf` and a `data/` folder with the certificate, a Lean file and a checking script.

- [`preprints/D4`](preprints/D4): every sphere packing in ℝ⁴ has density below 0.629521681653. The proof uses a scalar Cohn–Elkies function and a two-point kernel on the neighbours of each centre. The kernel only needs nonnegative energy on actual neighbourhoods, not positive definiteness. A census of neighbour counts gives a floor for that energy. The new step moves the slack of the triangle inequality onto pairs of neighbours on opposite sides of the centre, and a short Cauchy–Schwarz lemma bounds the gain. The Lean file proves that lemma, the finite inequality and the exact ledger, and states the interval-certified sign checks as hypotheses.

## Bounds

| Dimension | Best published | Our upper bound | Method | Folder |
|---:|---:|---:|---|---|
| 4 | 0.636108 (Cohn-de Laat-Salmon) | 0.629521681653 | Local-energy bound with a neighbour-count floor and far-pair reallocation | [D4](preprints/D4) |

The densest known packing in four dimensions is the lattice D4, with density π²/16 ≈ 0.616850.

## References

- Henry Cohn, David de Laat and Andrew Salmon, [Three-point bounds for sphere packing](https://arxiv.org/abs/2206.15373).
- Henry Cohn and Noam Elkies, New upper bounds on sphere packings I, Ann. of Math. 157 (2003), 689–714.
- Rupert Li, [Dual linear programming bounds for sphere packing via discrete reductions](https://arxiv.org/abs/2206.09876).

## Other GitHub repositories

- [alexlegeartis/SpherePackingUpperBounds](https://github.com/alexlegeartis/SpherePackingUpperBounds)
