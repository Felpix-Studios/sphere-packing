# Sphere packing upper bounds

Preprints and certificates for upper bounds on sphere packing density. Every bound covers all packings, lattice or not, periodic or not. These are upper bounds only. They do not prove that any packing is optimal.

## Layout

Each folder under [`preprints/`](preprints) holds one result: a `paper.pdf`, its LaTeX source, certificate data, and checking programs.

- [`preprints/D4`](preprints/D4): every sphere packing in ℝ⁴ has density below 0.629521681653. The proof uses a scalar Cohn–Elkies function and a two-point kernel on the neighbours of each centre. The kernel only needs nonnegative energy on actual neighbourhoods, not positive definiteness. A census of neighbour counts gives a floor for that energy. The new step moves the slack of the triangle inequality onto pairs of neighbours on opposite sides of the centre, and a short Cauchy–Schwarz lemma bounds the gain.

## D4 computer-assisted proof update

The D4 folder now contains the complete non-Lean computer-assisted proof package: exact certificate data, written component proofs, all five verification stages, independent kernel reconstruction, exact kernel-link checks, negative controls, and the reproducible preprint source. The package does not depend on a private research checkout.

From `preprints/D4`:

```sh
python3 -m pip install -r verify/requirements.txt
python3 verify/verify_all.py --out /tmp/d4-full-check --mode full --workers 2
```

The full run checks the scalar and kernel signs, 112 cyclic branches, the 165,503-vector census, 124 refined floors, both kernel-box trees, the independent reconstruction, and the final exact inequality. Quick mode is only a development check and is not a full global replay.

The folder also contains a separate Lean 4 formalization of the complete bound in `preprints/D4/lean`. Its main theorem takes only the packing as input, with no `sorry` and no added axiom; 125 finite checks use `native_decide`. The two proofs share no code or results. See [`preprints/D4/FORMALIZATION_STATUS.md`](preprints/D4/FORMALIZATION_STATUS.md).

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
