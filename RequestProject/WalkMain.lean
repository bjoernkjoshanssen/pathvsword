import RequestProject.WalkEndgame
import RequestProject.WalkBase

/-!
# Every uniquely accepting walk for `z_k` has at least `k+6` states

This file states and proves the main result of Sections 4–6 of
`anevsanseparationv4.tex` (the lower bound `A_N(z_k) ≥ k+6` in its walk form), by
splitting it into the base cases `k ∈ {3,6,9,12,15}` and the case `k ≥ 18`, exactly as in
the "Conclusion of the proof" of Section 6 of the source.

## What is proved

The supporting development is complete for the following parts of the source:

* Section 2 (`sec:prelim`): `isUAWalk_of_uniquelyAccepts` (the direction of Lemma 2.1
  `lem:walk` used for the lower bound);
* Section 4 (`sec:tools`): `rotation` (`lem:rotation`), `zw_eq_pair` (`lem:pairs`),
  `shift_classification` (`cor:shifts`), `no_square` (`lem:squarefree`),
  `twovisit_run` (`lem:twovisit`), `aligned_block` (`lem:block`),
  `crossing` (`lem:cross`);
* Section 5.1 (`sec:budget`): `count_nonrun`, `count_run` (`eq:count`, `eq:vA`),
  `budget` (`eq:budget`) and `bridge_single_parity` (`b₁ ≡ s₀ mod 2`);
* Section 5.2, Step 1 of Lemma 5.3 (`lem:gamma`): `cluster_cycle`, `period_refine`,
  `exists_stretch_min`, `ell_le_four`, `exists_Stretch` and `exists_maximal_Stretch`,
  producing a *maximal* stretch `Stretch k c` with `ℓ ≤ 4` and `t ≥ 3`, all of whose
  `γ`-states are visited only inside the stretch;
* Section 5.3 (`sec:surgery`): all the surgeries — `narrow_prefix_skip`,
  `narrow_tail_skip`, `narrow_prefix_insert`, `narrow_tail_insert`,
  `narrow_prefix_pair`, `narrow_tail_pair`, `narrow_mixed_pair` (`lem:narrow`),
  `wide_chords_nested` and `wide_chord_fold` (`lem:wide`), `foldloop_lt`/`foldloop_gt`
  (`cor:foldloop`), `lasso_u1`/`lasso_u2` (`lem:lasso`);
* Section 5.4 (`sec:block`): `positions_*` (`lem:positions`);
* Section 5.5 (`sec:bridges`): `bridge_prefix`, `bridge_tail`, `bridge_wide_prefix`,
  `bridge_wide_tail` (the surgeries behind `lem:bridgeparity`);
* Section 6.1: `double_passage` (`lem:dichotomy`);
* Section 6.2: `shapes` (`cor:shapes`), the arithmetic that leaves only the three shapes
  (a), (b), (c) — including the exclusion of `ℓ = 3`, the one place where `k ≡ 0 (mod 3)`
  is used;
* the assembly of the endgame, `no_small_walk_large`, and the reduction of the base cases
  to a search over colourings by `Fin (k+5)`, `walk_relabel`.

## What is still missing

Exactly one `sorry` remains, and it is the finite search that the source performs by
machine and that the task allows to be left unproved:

* `base_search` (in `RequestProject/WalkBase.lean`) — the cases `k ∈ {3,6,9,12,15}`,
  settled in the source by the exhaustive machine search of Section 7
  (`sec:verification`).  It is a property of the finitely many colourings
  `{0,…,3k+7} → Fin (k+5)` and is decidable in principle.

All the leaves of the structure theory of Sections 5 and 6 are proved: Lemma 5.3
(`gamma_offCycle_count`), Lemma 5.11 (`aligned_nonempty`), Lemma 5.13
(`bridgeCount_eq_zero_of_ell_one`), Lemma 5.14(a) (`bridgeCount_le_one_of_ell_two`) and
the four endgame propositions `ell_one_impossible` (`prop:ell1`), `ell_four_impossible`
(`prop:ell4`), `ell_two_clean_impossible` (`prop:ell2clean`) and
`ell_two_bridge_impossible` (`prop:ell2bridge`).
-/

namespace AneVsAn

set_option autoImplicit false

/-- **Sections 4–6 of `anevsanseparationv4.tex`**: for `k ≥ 3` with `k ≡ 0 (mod 3)`,
every uniquely accepting walk for `z_k` has at least `k+6` distinct states.
Together with Lemma 2.1 (`lem:walk`) this is the lower bound of Theorem 1.2
(`thm:main`).

The proof follows the "Conclusion of the proof" of Section 6 of the source: the cases
`k ∈ {3,6,9,12,15}` are the machine search `walk_card_lower_base`, and for `k ≥ 18` the
structure theory of Sections 5–6 gives the contradiction `no_small_walk_large`.  See the
module docstring for the one statement that is still `sorry`, the machine search of
Section 7. -/
theorem walk_card_lower {k : ℕ} (hk : 3 ≤ k) (hk3 : k % 3 = 0) {S : Type} [DecidableEq S]
    (c : ℕ → S) (hc : IsUAWalk (zw k) (wlen k) c) :
    k + 6 ≤ (walkStates (wlen k) c).card := by
  have hc' : IsUAWalk (zw k) (3 * k + 7) c := hc
  rcases (by omega : k ≤ 15 ∨ 18 ≤ k) with hsmall | hbig
  · exact walk_card_lower_base hk hsmall hk3 c hc'
  · by_contra hcon
    exact no_small_walk_large hbig hk3 hc' (by
      have : (walkStates (3 * k + 7) c).card < k + 6 := by
        simpa [wlen] using hcon
      omega)

end AneVsAn
