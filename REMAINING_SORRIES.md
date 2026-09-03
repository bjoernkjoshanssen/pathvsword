# The remaining `sorry` of the lower bound

The formalization of Theorem 1.2 of `anevsanseparationv4.tex` is complete except for the
single leaf statement listed below, which is the machine computation of Section 7 of the
source and which the task explicitly allows to be left unproved.

Everything else — the two upper bounds, the master lemmas of Section 4, the budget count
of Section 5.1, the cycle lemma of Section 5.2, all the surgeries of Sections 5.3–5.5 and
6.1, the position and counting lemmas of Sections 5.4–5.6, the arithmetic of the surviving
shapes (Corollary 6.2), the four endgame propositions 6.3, 6.5, 6.7 and 6.8, and the
assembly of the whole argument into
`AneVsAn.walk_card_lower` → `AneVsAn.AN_lower` → `AneVsAn.main_theorem` — is proved.

## The statement that is a finite search (decidable in principle)

| Lean name | Source result |
|-----------|---------------|
| `base_search` (in `RequestProject/WalkBase.lean`) | Section 7 (`sec:verification`): for `k ∈ {3,6,9,12,15}` no colouring of the `3k+8` positions of `z_k` by `k+5` states is a uniquely accepting walk |

This is the exhaustive machine search that `anevsanseparationv4.tex` performs by computer.
It is a finite check: the statement is about the `(k+5)^(3k+8)` colourings
`{0,…,3k+7} → Fin (k+5)`, and for each of them unique acceptance is decided by inspecting
the finitely many paths of length `n` in the resulting walk graph.  (As written it is not
literally an instance of Lean's `Decidable` class, because a colouring is given as a
function on all of `ℕ` and unique acceptance quantifies over all pairs consisting of a
word and a path; but both only depend on the restrictions to `{0,…,n}`, so the statement
is equivalent to a finite check.)

The reduction of the general base case to this finite form — every walk with at most `k+5`
states can be recoloured by `Fin (k+5)` — is proved (`walk_relabel`).

Consequently `#print axioms AneVsAn.main_theorem` reports `propext`, `Classical.choice`,
`Quot.sound` and `sorryAx`, the last one coming solely from `base_search`.

## Where the endgame propositions are proved

| Lean name | Source result | File |
|-----------|---------------|------|
| `gamma_offCycle_count` | Steps 2, 4, 5 of Lemma 5.3 (`lem:gamma`), `eq:dzero` | `RequestProject/WalkOffCycle.lean` |
| `aligned_nonempty` | Lemma 5.11 (`lem:Inonempty`) | `RequestProject/WalkAligned.lean` |
| `bridgeCount_eq_zero_of_ell_one` | Lemma 5.13 (`lem:bridgeparity`), last sentence | `RequestProject/WalkBridgeParity.lean` |
| `bridgeCount_le_one_of_ell_two` | Lemma 5.14(a) (`lem:twoodd`) | `RequestProject/WalkChordPair.lean` |
| `ell_one_impossible` | Proposition 6.3 (`prop:ell1`) | `RequestProject/WalkEndgame.lean` |
| `ell_four_impossible` | Proposition 6.5 (`prop:ell4`) | `RequestProject/WalkEll4.lean` |
| `ell_two_clean_impossible` | Proposition 6.7 (`prop:ell2clean`) | `RequestProject/WalkEll2.lean` |
| `ell_two_bridge_impossible` | Proposition 6.8 (`prop:ell2bridge`) | `RequestProject/WalkEll2Bridge.lean` |
