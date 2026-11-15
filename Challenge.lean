module

public import Mathlib.Order.Lattice.Nat

@[expose] public section

/-!
# Lower bounds for the Gallai–van der Waerden numbers `GW(r; 5, 3)` and `GW(r; 6, 3)`: the statement

This file is the statement of record. It imports only Mathlib, defines the notions the statements
use, and states the results with `sorry`. `Solution.lean` proves every statement; `comparator.json`
names the compared theorems. The definitions below must agree exactly with the ones the proof uses
(Comparator checks this), so they are spelled out here in full.

## Gallai–van der Waerden numbers

Write `[1, n] = {1, …, n}`. An *exact `r`-colouring* of `[1, n]` is a colouring of `[1, n]` with
`r` colours in which every colour occurs. An arithmetic progression (AP) always has common
difference `d ≥ 1`. A `k`-term AP `x, x + d, …, x + (k - 1)d` is *rainbow* when its `k` terms have
pairwise distinct colours, and an `l`-term AP is *monochromatic* when all its terms have the same
colour. The Gallai–van der Waerden number `GW(r; k, l)` of Mao, Ozeki, Robertson and Wang
(J. Combin. Theory Ser. A 193 (2023) 105672, Definition 1.15) is the least `M` such that, for every
`n ≥ M`, every exact `r`-colouring of `[1, n]` contains a rainbow `k`-term AP or a monochromatic
`l`-term AP. The definitions below are those of the registered entry PALOMAR-2026-11-12-000009.

## The results (Quantavane, November 2026)

For `r ≤ 4`, `GW(r; 5, 3)` is the van der Waerden number `w(r; 3)` (MORW, Proposition 4.1), which
is `3, 9, 27, 76`. For `r ≥ 5` only lower bounds are known; these are proved here.

* `exists_good_row5`: for `5 ≤ r ≤ 17` the interval `[1, len5 r]` has an exact `r`-colouring with
  no rainbow 5-term AP and no monochromatic 3-term AP, where `len5 r` is

  | `r` | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 |
  |---|---|---|---|---|---|---|---|---|---|---|---|---|---|
  | `len5 r` | 85 | 85 | 80 | 80 | 78 | 78 | 78 | 77 | 73 | 73 | 59 | 59 | 52 |

* `lt_of_gwProperty_row5`, `lt_GW_row5`: hence `GW(r; 5, 3) ≥ len5 r + 1`; for instance
  `GW(5; 5, 3) ≥ 86` and `GW(6; 5, 3) ≥ 86`.
* `exists_canonical_row5`: some colouring of `[1, 85]`, with any number of colours, has neither a
  rainbow 5-term AP nor a monochromatic 3-term AP; that is, the canonical number `H(5, 3)` is at
  least `86` (more than `w(4; 3) = 76`).
* `exists_good_row6`, `lt_of_gwProperty_row6`, `lt_GW_row6`: `[1, 86]` has a good exact
  6-colouring and `[1, 87]` good exact 7- and 8-colourings for rainbow 6-term and monochromatic
  3-term APs, so `GW(6; 6, 3) ≥ 87`, `GW(7; 6, 3) ≥ 88` and `GW(8; 6, 3) ≥ 88`.
-/

namespace Gw53

/-- `c` is a *good exact `r`-colouring of `[1, n]`* for rainbow `k`-term and monochromatic `l`-term
arithmetic progressions: every colour `col : Fin r` occurs on `[1, n]`; no `x, x + d, …, x + (k - 1)d`
in `[1, n]` with `d ≥ 1` has `k` pairwise distinct colours; and no `x, x + d, …, x + (l - 1)d` in
`[1, n]` with `d ≥ 1` has all its terms of one colour. The colouring is a function on all of `ℕ`;
its values outside `[1, n]` play no role. -/
def IsGoodExactColouring (r k l n : ℕ) (c : ℕ → Fin r) : Prop :=
  (∀ col : Fin r, ∃ x, 1 ≤ x ∧ x ≤ n ∧ c x = col) ∧
  (∀ x d : ℕ, 1 ≤ x → 1 ≤ d → x + (k - 1) * d ≤ n →
    ¬ ∀ i < k, ∀ j < k, i ≠ j → c (x + i * d) ≠ c (x + j * d)) ∧
  (∀ x d : ℕ, 1 ≤ x → 1 ≤ d → x + (l - 1) * d ≤ n → ¬ ∀ j < l, c (x + j * d) = c x)

/-- `M` has the defining property of the Gallai–van der Waerden number `GW(r; k, l)`
(Mao–Ozeki–Robertson–Wang, JCTA 2023, Def. 1.15): for every `n ≥ M`, every exact `r`-colouring of
`[1, n]` contains a rainbow `k`-term AP or a monochromatic `l`-term AP, that is, no `[1, n]` with
`n ≥ M` has a good exact `r`-colouring. -/
def GWProperty (r k l M : ℕ) : Prop :=
  ∀ n ≥ M, ∀ c : ℕ → Fin r, ¬ IsGoodExactColouring r k l n c

/-- `GW(r; k, l)`: the least `M` with `GWProperty r k l M`. Lean's `sInf` of the empty set of
natural numbers is `0`; the Gallai–van der Waerden theorem says that the set is not empty, but it is
not formalised here, so `lt_GW_row5` and `lt_GW_row6` assume that some `M` has the property. -/
noncomputable def GW (r k l : ℕ) : ℕ := sInf {M | GWProperty r k l M}

/-- The lengths of the good exact colourings of the row `(5, 3)`, for `5 ≤ r ≤ 17`. -/
def len5 (r : ℕ) : ℕ :=
  [85, 85, 80, 80, 78, 78, 78, 77, 73, 73, 59, 59, 52].getD (r - 5) 0

/-- **Row `(5, 3)`: good exact colourings.** For `5 ≤ r ≤ 17` there is an exact `r`-colouring of
`[1, len5 r]` with no rainbow 5-term AP and no monochromatic 3-term AP. -/
theorem exists_good_row5 (r : ℕ) (h5 : 5 ≤ r) (h17 : r ≤ 17) :
    ∃ c : ℕ → Fin r, IsGoodExactColouring r 5 3 (len5 r) c := by
  sorry

/-- **Row `(5, 3)`: `GW(r; 5, 3) ≥ len5 r + 1` for `5 ≤ r ≤ 17`** (threshold form). Every `M` with
the defining property exceeds `len5 r`. -/
theorem lt_of_gwProperty_row5 (r : ℕ) (h5 : 5 ≤ r) (h17 : r ≤ 17) (M : ℕ)
    (hM : GWProperty r 5 3 M) : len5 r < M := by
  sorry

/-- **Row `(5, 3)`: `GW(r; 5, 3) ≥ len5 r + 1` for `5 ≤ r ≤ 17`**, for the number itself, given that
some `M` has the property (`hex`, the Gallai–van der Waerden theorem, not formalised here). -/
theorem lt_GW_row5 (r : ℕ) (h5 : 5 ≤ r) (h17 : r ≤ 17) (hex : ∃ M, GWProperty r 5 3 M) :
    len5 r < GW r 5 3 := by
  sorry

/-- **`H(5, 3) ≥ 86`.** Some colouring of `[1, 85]` (by natural numbers, with any number of colours)
has no rainbow 5-term AP and no monochromatic 3-term AP. -/
theorem exists_canonical_row5 :
    ∃ c : ℕ → ℕ,
      (∀ x d : ℕ, 1 ≤ x → 1 ≤ d → x + 4 * d ≤ 85 →
        ¬ ∀ i < 5, ∀ j < 5, i ≠ j → c (x + i * d) ≠ c (x + j * d)) ∧
      (∀ x d : ℕ, 1 ≤ x → 1 ≤ d → x + 2 * d ≤ 85 → ¬ ∀ j < 3, c (x + j * d) = c x) := by
  sorry

/-- **Row `(6, 3)`: good exact colourings** of `[1, 86]` with 6 colours and of `[1, 87]` with 7 and
with 8 colours, with no rainbow 6-term AP and no monochromatic 3-term AP. -/
theorem exists_good_row6 :
    (∃ c : ℕ → Fin 6, IsGoodExactColouring 6 6 3 86 c) ∧
    (∃ c : ℕ → Fin 7, IsGoodExactColouring 7 6 3 87 c) ∧
    (∃ c : ℕ → Fin 8, IsGoodExactColouring 8 6 3 87 c) := by
  sorry

/-- **Row `(6, 3)`: `GW(6; 6, 3) ≥ 87`, `GW(7; 6, 3) ≥ 88`, `GW(8; 6, 3) ≥ 88`** (threshold form). -/
theorem lt_of_gwProperty_row6 (M : ℕ) :
    (GWProperty 6 6 3 M → 86 < M) ∧ (GWProperty 7 6 3 M → 87 < M) ∧
    (GWProperty 8 6 3 M → 87 < M) := by
  sorry

/-- **Row `(6, 3)`: `GW(6; 6, 3) ≥ 87`, `GW(7; 6, 3) ≥ 88`, `GW(8; 6, 3) ≥ 88`**, for the numbers
themselves, given that thresholds exist. -/
theorem lt_GW_row6 :
    ((∃ M, GWProperty 6 6 3 M) → 86 < GW 6 6 3) ∧ ((∃ M, GWProperty 7 6 3 M) → 87 < GW 7 6 3) ∧
    ((∃ M, GWProperty 8 6 3 M) → 87 < GW 8 6 3) := by
  sorry

end Gw53
