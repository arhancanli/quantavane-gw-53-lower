module

public import Gw53

public section

/-!
# Proofs of the statements in `Challenge.lean`

Each theorem below has exactly the statement of its counterpart in `Challenge.lean` (Comparator
checks this, together with the definitions the statements use, which come from `Gw53.Defs`).

* `exists_good_row5`, `exists_good_row6`: the explicit colourings of `Gw53.Colourings`, checked by
  `decide +kernel` through the Boolean test of `Gw53.Check`;
* the threshold and `GW` forms: a good exact colouring of `[1, n]` puts every threshold above `n`
  (`lt_of_good`, `lt_GW_of_good`);
* `exists_canonical_row5`: the 5-colouring of `[1, 85]` read as a colouring by natural numbers.
-/

namespace Gw53

theorem exists_good_row5 (r : ℕ) (h5 : 5 ≤ r) (h17 : r ≤ 17) :
    ∃ c : ℕ → Fin r, IsGoodExactColouring r 5 3 (len5 r) c := by
  rcases (by omega : r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 ∨ r = 10 ∨ r = 11 ∨ r = 12 ∨ r = 13 ∨
    r = 14 ∨ r = 15 ∨ r = 16 ∨ r = 17) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨cola5, gooda5⟩
  · exact ⟨cola6, gooda6⟩
  · exact ⟨cola7, gooda7⟩
  · exact ⟨cola8, gooda8⟩
  · exact ⟨cola9, gooda9⟩
  · exact ⟨cola10, gooda10⟩
  · exact ⟨cola11, gooda11⟩
  · exact ⟨cola12, gooda12⟩
  · exact ⟨cola13, gooda13⟩
  · exact ⟨cola14, gooda14⟩
  · exact ⟨cola15, gooda15⟩
  · exact ⟨cola16, gooda16⟩
  · exact ⟨cola17, gooda17⟩

theorem lt_of_gwProperty_row5 (r : ℕ) (h5 : 5 ≤ r) (h17 : r ≤ 17) (M : ℕ)
    (hM : GWProperty r 5 3 M) : len5 r < M := by
  obtain ⟨c, hc⟩ := exists_good_row5 r h5 h17
  exact lt_of_good hc hM

theorem lt_GW_row5 (r : ℕ) (h5 : 5 ≤ r) (h17 : r ≤ 17) (hex : ∃ M, GWProperty r 5 3 M) :
    len5 r < GW r 5 3 := by
  obtain ⟨c, hc⟩ := exists_good_row5 r h5 h17
  exact lt_GW_of_good hc hex

theorem exists_canonical_row5 :
    ∃ c : ℕ → ℕ,
      (∀ x d : ℕ, 1 ≤ x → 1 ≤ d → x + 4 * d ≤ 85 →
        ¬ ∀ i < 5, ∀ j < 5, i ≠ j → c (x + i * d) ≠ c (x + j * d)) ∧
      (∀ x d : ℕ, 1 ≤ x → 1 ≤ d → x + 2 * d ≤ 85 → ¬ ∀ j < 3, c (x + j * d) = c x) := by
  obtain ⟨_, hrb, hmono⟩ := gooda5
  refine ⟨fun x => (cola5 x : ℕ), ?_, ?_⟩
  · intro x d hx hd hxd hall
    exact hrb x d hx hd hxd fun i hi j hj hij h => hall i hi j hj hij (congrArg Fin.val h)
  · intro x d hx hd hxd hall
    exact hmono x d hx hd hxd fun j hj => Fin.ext (hall j hj)

theorem exists_good_row6 :
    (∃ c : ℕ → Fin 6, IsGoodExactColouring 6 6 3 86 c) ∧
    (∃ c : ℕ → Fin 7, IsGoodExactColouring 7 6 3 87 c) ∧
    (∃ c : ℕ → Fin 8, IsGoodExactColouring 8 6 3 87 c) :=
  ⟨⟨colb6, goodb6⟩, ⟨colb7, goodb7⟩, ⟨colb8, goodb8⟩⟩

theorem lt_of_gwProperty_row6 (M : ℕ) :
    (GWProperty 6 6 3 M → 86 < M) ∧ (GWProperty 7 6 3 M → 87 < M) ∧
    (GWProperty 8 6 3 M → 87 < M) :=
  ⟨fun h => lt_of_good goodb6 h, fun h => lt_of_good goodb7 h, fun h => lt_of_good goodb8 h⟩

theorem lt_GW_row6 :
    ((∃ M, GWProperty 6 6 3 M) → 86 < GW 6 6 3) ∧ ((∃ M, GWProperty 7 6 3 M) → 87 < GW 7 6 3) ∧
    ((∃ M, GWProperty 8 6 3 M) → 87 < GW 8 6 3) :=
  ⟨fun h => lt_GW_of_good goodb6 h, fun h => lt_GW_of_good goodb7 h, fun h => lt_GW_of_good goodb8 h⟩

end Gw53
