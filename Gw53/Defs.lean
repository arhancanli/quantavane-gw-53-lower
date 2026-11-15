module

public import Mathlib.Order.Lattice.Nat

@[expose] public section

/-!
# Definitions used by the proof

These are the four definitions of `Challenge.lean`, with the same imports and the same text, so
that the proof is about exactly the notions the statement uses (Comparator checks that the
declarations agree). See `Challenge.lean` for the mathematical account.
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

end Gw53
