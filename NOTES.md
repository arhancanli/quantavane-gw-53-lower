# Notes: what is proved and how it was checked (15 November 2026)

## What is proved

Everything below is proved in Lean 4 (v4.35.0, Mathlib v4.35.0) with no `sorry`, no `native_decide`
and only the axioms `propext`, `Classical.choice` and `Quot.sound`. The statements of record are in
`Challenge.lean`; `comparator.json` names the seven compared theorems.

- `Gw53.exists_good_row5`: for `5 ≤ r ≤ 17`, a good exact `r`-colouring of `[1, len5 r]` for rainbow
  5-term and monochromatic 3-term progressions, `len5 r = 85, 85, 80, 80, 78, 78, 78, 77, 73, 73, 59,
  59, 52`.
- `Gw53.lt_of_gwProperty_row5`, `Gw53.lt_GW_row5`: `GW(r; 5, 3) > len5 r` (threshold form; number form
  given that a threshold exists).
- `Gw53.exists_canonical_row5`: a colouring `ℕ → ℕ` of `[1, 85]` with no rainbow 5-term and no
  monochromatic 3-term progression (`H(5, 3) ≥ 86`).
- `Gw53.exists_good_row6`, `Gw53.lt_of_gwProperty_row6`, `Gw53.lt_GW_row6`: good exact 6-, 7- and
  8-colourings of `[1, 86]`, `[1, 87]`, `[1, 87]` for `(k, l) = (6, 3)`, and `GW(6; 6, 3) > 86`,
  `GW(7; 6, 3) > 87`, `GW(8; 6, 3) > 87`.

The colourings rest on 32 kernel checks by `decide +kernel`: for each of the sixteen colourings,
`allCols` (every colour occurs) and `rangeTest` over all differences. `good_of_tests` (proved for
every input) turns them into `IsGoodExactColouring`. `scripts/make_colourings.py` read the thirteen
colourings of the row `(5, 3)` from `gw/k5/witnesses_k5l3.txt` of the public data repository, built
the three of the row `(6, 3)` by end extension, and checked all sixteen by brute force; the Lean
proof relies on none of this.

## Line counts

| File | Lines |
|---|---|
| `Challenge.lean` | 125 (6,969 bytes) |
| `Solution.lean` | 79 |
| `Gw53.lean` | 5 |
| `Gw53/Defs.lean` | 44 |
| `Gw53/Check.lean` | 236 |
| `Gw53/Colourings.lean` | 294 (generated) |
| `scripts/CheckAxioms.lean` | 19 |

Every `.lean` file starts with `module`; `Challenge.lean` imports only Mathlib
(`Mathlib.Order.Lattice.Nat`).

## Checks run (Mac, Apple silicon, Lean v4.35.0)

All on a fresh clone of commit `d6d6968699269193aee1b78cf3a01067fd125ad9` (the commit before this
file was added; no Lean file changed since), with the Lake packages of the pinned Mathlib checkout and
the project's own modules built from scratch (a local check script; its log is kept outside this
repository).

1. `lake build`: every module built in 19 s. `Challenge` warns seven times (declaration uses
   `sorry`, as intended).
2. `lake env lean scripts/CheckAxioms.lean`: `[propext, Classical.choice, Quot.sound]` for each of
   the seven theorems.
3. `lake comparator` needs bubblewrap (Linux namespaces) and does not run on macOS. In its place,
   steps 4 and 6 were run by hand.
4. Statement comparison: every constant reachable from the types of the compared theorems (following
   definition values, not proofs) was printed with `pp.all` and hashes in the Challenge and in the
   Solution environment. Apart from the module of the four own definitions (`Challenge` against
   `Gw53.Defs`), the two outputs (7 roots, 349 constants) are identical.
5. Red controls (`RedControl.lean`): the 5-colouring of `[1, 85]` on `[1, 86]`, the 5-colouring with
   point 1 recoloured, the 5-colouring tested for rainbow 4-term progressions, the extended 6-colouring
   tested for rainbow 5-term progressions, and a missing seventeenth colour of the 16-colouring are all
   rejected by the kernel; the 17-colouring and its colour test pass.
6. Kernel replays: `leanexport` wrote both modules with the compared theorems as targets; the Solution
   export (5.8 MB) was replayed through every kernel bundled with the toolchain (each run would have
   been stopped had it passed 7 GB of memory; none did):

   ```
   leanchecker            rc 0     5 s
   nanoda                 rc 0     2 s   0.3 GB
   con-ron                rc 0     1 s   accepted 1805 declarations (--verified)
   leanchecker-paranoid   rc 0     7 s
   lean4lean              rc 0     7 s   checked 1802 declarations
   con-leche              rc 0     2 s   0.7 GB   accepted 1805 declarations (--verified)
   ```

   NanoDa with unpermitted axioms as a hard error: Solution export exit 0; Challenge export exit 1
   (`export file declares unpermitted axiom "sorryAx"`), as it should. `Lean.ofReduceBool` does not
   occur in the Solution export. SHA-256 of the exports: `solution.ndjson`
   `ab65e509cef177d3a80746e9faf8433770d828ae42b90bcb4c7c8325af7a49e5`, `challenge.ndjson`
   `2f0229b9e656f812601ca50f85067f0402b509f43466c4c019847046a9028c73`.

## What remains

- Palomar's mechanical preflight (the workflow above, on GitHub's Linux runners) has not run: it needs
  the repository to be public on GitHub.
- No review outside Quantavane's agents.
- Not formalized: the Gallai–van der Waerden theorem (existence of a threshold), the paper's Lemma 2.3
  (the extended colourings are checked directly), any upper bound for these rows.
