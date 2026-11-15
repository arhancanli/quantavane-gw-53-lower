module

public import Gw53.Defs

@[expose] public section

/-!
# A kernel test for good exact colourings, and its soundness

A colouring is stored as a natural number `B` in base 32: point `y ≥ 1` gets the digit `y - 1`, and
with `r` colours its colour is that digit reduced mod `r` (`cv r B y`, read by the kernel with its
built-in `Nat.shiftRight`, `Nat.land` and `Nat.mod`; `digitCol` is the same colouring as a function
to `Fin r`).

The tests below are written with structural recursion and the `Nat` primitives only, so that Lean's
kernel (and the other kernels that replay the proof) evaluate them with little work and little
memory:

* `someEqK r B x d k`: two of the terms `x + i d` (`i < k`) have the same colour;
* `someNeL r B x d l`: one of the terms `x + j d` (`j < l`) has a colour other than that of `x`;
* `rowTest r B k l n d cnt`: for the difference `d`, every `x` with `1 ≤ x ≤ cnt` passes the
  `k`-term test if `x + (k - 1)d ≤ n`, and the `l`-term test if `x + (l - 1)d ≤ n`;
* `rangeTest r B k l n m lo cnt`: `rowTest` with `cnt = n - (m - 1)d` for every difference `d`
  with `lo ≤ d < lo + cnt` (`m = min k l`: a progression of `m` terms or more starting at `x ≥ 1`
  ends in `[1, n]` only if `x ≤ n - (m - 1)d`);
* `allCols r B n s`: every colour `t < s` occurs on `[1, n]`.

`good_of_tests` proves that if `allCols` passes and `rowTest` passes for every difference
`d ≤ D`, where `(m - 1)(D + 1) > n`, the colouring `digitCol r B` is a good exact `r`-colouring of
`[1, n]`. The range of differences is split into pieces (`rangeTest_spec`), each checked in its own
declaration, so that each kernel check is small.
-/

namespace Gw53

/-- The colour of point `y`: the base-32 digit `y - 1` of `B`, reduced mod `r`. -/
def cv (r B y : ℕ) : ℕ := Nat.mod (Nat.land (Nat.shiftRight B (Nat.mul 5 (Nat.sub y 1))) 31) r

/-- The same colouring as a function to `Fin r`. -/
def digitCol (r : ℕ) (hr : 0 < r) (B y : ℕ) : Fin r := ⟨cv r B y, Nat.mod_lt _ hr⟩

/-- Some term `x + i d` with `i < m` has the colour of `x + j d`. -/
def eqBefore (r B x d j : ℕ) : ℕ → Bool
  | 0 => false
  | i + 1 => Nat.beq (cv r B (Nat.add x (Nat.mul i d))) (cv r B (Nat.add x (Nat.mul j d))) ||
      eqBefore r B x d j i

/-- Two of the terms `x + i d` with `i < m` have the same colour. -/
def someEqK (r B x d : ℕ) : ℕ → Bool
  | 0 => false
  | j + 1 => eqBefore r B x d j j || someEqK r B x d j

/-- One of the terms `x + j d` with `j < m` has a colour other than that of `x`. -/
def someNeL (r B x d : ℕ) : ℕ → Bool
  | 0 => false
  | j + 1 => !Nat.beq (cv r B (Nat.add x (Nat.mul j d))) (cv r B x) || someNeL r B x d j

/-- For the difference `d`: every `x` with `1 ≤ x ≤ cnt` passes the `k`-term test if
`x + (k - 1)d ≤ n`, and the `l`-term test if `x + (l - 1)d ≤ n`. -/
def rowTest (r B k l n d : ℕ) : ℕ → Bool
  | 0 => true
  | x + 1 =>
    (!Nat.ble (Nat.add (x + 1) (Nat.mul (Nat.sub k 1) d)) n || someEqK r B (x + 1) d k) &&
    (!Nat.ble (Nat.add (x + 1) (Nat.mul (Nat.sub l 1) d)) n || someNeL r B (x + 1) d l) &&
    rowTest r B k l n d x

/-- `rowTest` with `cnt = n - (m - 1)d` for every difference `d` with `lo ≤ d < lo + cnt`. -/
def rangeTest (r B k l n m lo : ℕ) : ℕ → Bool
  | 0 => true
  | c + 1 => rowTest r B k l n (Nat.add lo c) (Nat.sub n (Nat.mul (Nat.sub m 1) (Nat.add lo c))) &&
      rangeTest r B k l n m lo c

/-- Colour `t` occurs at one of the points `1, …, m`. -/
def colTest (r B t : ℕ) : ℕ → Bool
  | 0 => false
  | y + 1 => Nat.beq (cv r B (y + 1)) t || colTest r B t y

/-- Every colour `t < s` occurs at one of the points `1, …, n`. -/
def allCols (r B n : ℕ) : ℕ → Bool
  | 0 => true
  | t + 1 => colTest r B t n && allCols r B n t

/-! ## Soundness -/

theorem beq_iff {a b : ℕ} : Nat.beq a b = true ↔ a = b := ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

theorem eqBefore_spec {r B x d j : ℕ} : ∀ m, eqBefore r B x d j m = true →
    ∃ i < m, cv r B (x + i * d) = cv r B (x + j * d) := by
  intro m
  induction m with
  | zero => intro h; simp [eqBefore] at h
  | succ m ih =>
    intro h
    simp only [eqBefore, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨m, Nat.lt_succ_self m, beq_iff.mp h⟩
    · obtain ⟨i, hi, hi'⟩ := ih h
      exact ⟨i, Nat.lt_succ_of_lt hi, hi'⟩

theorem someEqK_spec {r B x d : ℕ} : ∀ m, someEqK r B x d m = true →
    ∃ i j, i < j ∧ j < m ∧ cv r B (x + i * d) = cv r B (x + j * d) := by
  intro m
  induction m with
  | zero => intro h; simp [someEqK] at h
  | succ m ih =>
    intro h
    simp only [someEqK, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨i, hi, hi'⟩ := eqBefore_spec m h
      exact ⟨i, m, hi, Nat.lt_succ_self m, hi'⟩
    · obtain ⟨i, j, hij, hj, h'⟩ := ih h
      exact ⟨i, j, hij, Nat.lt_succ_of_lt hj, h'⟩

theorem someNeL_spec {r B x d : ℕ} : ∀ m, someNeL r B x d m = true →
    ∃ j < m, cv r B (x + j * d) ≠ cv r B x := by
  intro m
  induction m with
  | zero => intro h; simp [someNeL] at h
  | succ m ih =>
    intro h
    simp only [someNeL, Bool.or_eq_true, Bool.not_eq_true'] at h
    rcases h with h | h
    · refine ⟨m, Nat.lt_succ_self m, fun he => ?_⟩
      have := beq_iff.mpr he
      simp_all
    · obtain ⟨j, hj, hj'⟩ := ih h
      exact ⟨j, Nat.lt_succ_of_lt hj, hj'⟩

theorem rowTest_spec {r B k l n d : ℕ} : ∀ cnt, rowTest r B k l n d cnt = true →
    ∀ x, 1 ≤ x → x ≤ cnt →
      (x + (k - 1) * d ≤ n → someEqK r B x d k = true) ∧
      (x + (l - 1) * d ≤ n → someNeL r B x d l = true) := by
  intro cnt
  induction cnt with
  | zero => intro _ x hx hx'; omega
  | succ c ih =>
    intro h x hx hx'
    simp only [rowTest, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    rcases Nat.lt_or_ge x (c + 1) with hlt | hge
    · exact ih h3 x hx (by omega)
    · have hx1 : x = c + 1 := by omega
      subst hx1
      refine ⟨fun hk => ?_, fun hl => ?_⟩
      · rcases h1 with h1 | h1
        · exfalso
          have : Nat.ble (c + 1 + (k - 1) * d) n = true := Nat.ble_eq.mpr hk
          exact absurd (h1 ▸ this) (by simp)
        · exact h1
      · rcases h2 with h2 | h2
        · exfalso
          have : Nat.ble (c + 1 + (l - 1) * d) n = true := Nat.ble_eq.mpr hl
          exact absurd (h2 ▸ this) (by simp)
        · exact h2

theorem rangeTest_spec {r B k l n m lo : ℕ} : ∀ cnt, rangeTest r B k l n m lo cnt = true →
    ∀ d, lo ≤ d → d < lo + cnt → rowTest r B k l n d (n - (m - 1) * d) = true := by
  intro cnt
  induction cnt with
  | zero => intro _ d h1 h2; omega
  | succ c ih =>
    intro h d h1 h2
    simp only [rangeTest, Bool.and_eq_true] at h
    rcases Nat.lt_or_ge d (lo + c) with hlt | hge
    · exact ih h.2 d h1 hlt
    · have : d = lo + c := by omega
      subst this
      exact h.1

theorem colTest_spec {r B t : ℕ} : ∀ m, colTest r B t m = true → ∃ y, 1 ≤ y ∧ y ≤ m ∧ cv r B y = t := by
  intro m
  induction m with
  | zero => intro h; simp [colTest] at h
  | succ m ih =>
    intro h
    simp only [colTest, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨m + 1, by omega, le_refl _, beq_iff.mp h⟩
    · obtain ⟨y, h1, h2, h3⟩ := ih h
      exact ⟨y, h1, by omega, h3⟩

theorem allCols_spec {r B n : ℕ} : ∀ s, allCols r B n s = true → ∀ t < s, ∃ y, 1 ≤ y ∧ y ≤ n ∧ cv r B y = t := by
  intro s
  induction s with
  | zero => intro _ t ht; omega
  | succ s ih =>
    intro h t ht
    simp only [allCols, Bool.and_eq_true] at h
    rcases Nat.lt_or_ge t s with hlt | hge
    · exact ih h.2 t hlt
    · have : t = s := by omega
      subst this
      exact colTest_spec n h.1

/-- **Soundness of the tests.** Let `2 ≤ m ≤ k, l` and `n < (m - 1)(D + 1)`. If every colour occurs
and every difference `d` with `1 ≤ d ≤ D` passes `rowTest` with `cnt = n - (m - 1)d`, then
`digitCol r hr B` is a good exact `r`-colouring of `[1, n]`. -/
theorem good_of_tests {r B k l n m D : ℕ} (hr : 0 < r) (hm : 2 ≤ m) (hmk : m ≤ k) (hml : m ≤ l)
    (hD : n < (m - 1) * (D + 1)) (hcols : allCols r B n r = true)
    (hrows : ∀ d, 1 ≤ d → d ≤ D → rowTest r B k l n d (n - (m - 1) * d) = true) :
    IsGoodExactColouring r k l n (digitCol r hr B) := by
  have key : ∀ x d t, m ≤ t → 1 ≤ x → 1 ≤ d → x + (t - 1) * d ≤ n →
      d ≤ D ∧ x ≤ n - (m - 1) * d := by
    intro x d t hmt hx hd hxd
    have h1 : (m - 1) * d ≤ (t - 1) * d := Nat.mul_le_mul_right d (by omega)
    refine ⟨?_, by omega⟩
    by_contra hdD
    have h2 : (m - 1) * (D + 1) ≤ (m - 1) * d := Nat.mul_le_mul_left (m - 1) (by omega)
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro col
    obtain ⟨y, h1, h2, h3⟩ := allCols_spec r hcols col.val col.isLt
    exact ⟨y, h1, h2, Fin.ext h3⟩
  · intro x d hx hd hxd hdist
    obtain ⟨hdD, hxc⟩ := key x d k hmk hx hd hxd
    have := (rowTest_spec _ (hrows d hd hdD) x hx hxc).1 hxd
    obtain ⟨i, j, hij, hj, heq⟩ := someEqK_spec k this
    exact hdist i (by omega) j hj (by omega) (Fin.ext heq)
  · intro x d hx hd hxd hall
    obtain ⟨hdD, hxc⟩ := key x d l hml hx hd hxd
    have := (rowTest_spec _ (hrows d hd hdD) x hx hxc).2 hxd
    obtain ⟨j, hj, hne⟩ := someNeL_spec l this
    exact hne (congrArg Fin.val (hall j hj))

/-- A good exact colouring of `[1, n]` puts every GW threshold above `n`. -/
theorem lt_of_good {r k l n : ℕ} {c : ℕ → Fin r} (hc : IsGoodExactColouring r k l n c) {M : ℕ}
    (hM : GWProperty r k l M) : n < M := by
  by_contra h
  exact hM n (Nat.le_of_not_lt h) c hc

/-- A good exact colouring of `[1, n]` puts `GW r k l` above `n` when some threshold exists. -/
theorem lt_GW_of_good {r k l n : ℕ} {c : ℕ → Fin r} (hc : IsGoodExactColouring r k l n c)
    (hex : ∃ M, GWProperty r k l M) : n < GW r k l :=
  le_csInf hex fun _ hM => lt_of_good hc hM

end Gw53
