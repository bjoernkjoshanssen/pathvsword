# Summary of changes for run c3c96fba-a568-4a20-9a7a-0e6ec10e3c7c
**Proposition 6.8 (`prop:ell2bridge`) is now proved, and with it the whole of Theorem 1.2 apart from the machine computation of Section 7.**

What I did this session:

1. **Completed `RequestProject/WalkEll2Bridge.lean`** with the main result `AneVsAn.ell2_bridge`, the formalization of Proposition 6.8 (the bridge shape `ℓ = 2`, `d₀ = 3`, `r_off = 1`, `(x₁,b₁,s₀) = (1,1,1)`). Following the three steps of the source:
   - *Step 1*: no narrow chord exists (Lemma 6.6(e)); the two `u`-states split as one `PU`-chord and the singleton (`pu_card_and_singleton`); the bridge's run visit lies outside the stretch and its non-run visit is a prefix or tail time (`bridge_visit_data`); the four loose-visit tallies then force the bridge to be a *tail* bridge with `β = r+1`, `δ = γ = r` and `r ≤ 1`.
   - *Step 2* (`r = 1`): the `γ`- and `PU`-chords occupy the prefix indices `0` and `1`; one order contradicts the Crossing Lemma 4.7, the other gives a `γ`-chord of even shift `k-2`, excluded by Corollary 5.8.
   - *Step 3* (`r = 0`): the bridge chord `(τ, 2k+6)` has odd length (Lemma 5.13), which leaves `L = 1` or `L = k+5`; both are killed by explicit second accepting paths that traverse the bridge chord three times (`bridge_loop_triple`, `bridge_insert_triple`).
   Every declaration carries a docstring naming the corresponding informal result of the source.

2. **Wired it into the endgame**: `AneVsAn.ell_two_bridge_impossible` in `RequestProject/WalkEndgame.lean` is no longer a `sorry`; it is now a direct application of `ell2_bridge`. Two hypotheses of that statement (the bound on the number of states and `x₁ = 1`) turned out to be unnecessary and were removed, and the call site was adjusted.

3. **Verification**: `lake build` succeeds; `AneVsAn.ell2_bridge`, `AneVsAn.ell_two_bridge_impossible` and `AneVsAn.shapes` depend only on `propext`, `Classical.choice`, `Quot.sound`. A project-wide search shows exactly one remaining `sorry`: `AneVsAn.base_search` in `RequestProject/WalkBase.lean`, the exhaustive finite search of Section 7 for `k ∈ {3,6,9,12,15}`, which the task explicitly allows to be left unproved. Consequently `AneVsAn.main_theorem` depends on the standard axioms plus `sorryAx`, coming solely from that finite check.

4. **Documentation**: rewrote `REMAINING_SORRIES.md` (now a single remaining item, plus a table of where each endgame proposition is proved) and refreshed the module docstrings of `WalkEndgame.lean` and `WalkMain.lean`, which still described the endgame leaves as unproved. `ARISTOTLE_SUMMARY.md` was left untouched, and the Properties table was updated to record Proposition 6.8 as proved.

Nothing was negated: all statements formalized from the paper have held up.


# Summary of changes for run 171eddda-df5b-48fb-8441-305f75191565
Yes — `A_N(1101000000100) ≥ 7` is now proved formally, and in fact `A_N = 7` exactly, so the separation for this length‑13 binary word is complete: `A_Ne(w) = 6 < 7 = A_N(w)`.

**New file `RequestProject/BinaryUnique.lean`** (no `sorry`; the whole project still builds, with the previously recorded open leaves of Theorem 1.2 untouched). Every declaration carries a docstring naming the corresponding informal notion in the attached source.

**Statements proved**
- `AneVsAn.Bin.AN_ge_seven : 7 ≤ AN 13 wbit` — the requested bound: every NFA that uniquely accepts `w = 1101000000100` (i.e. has exactly one accepting computation of length 13) has at least 7 states.
- `AneVsAn.Bin.AN_le_seven` and `AneVsAn.Bin.AN_eq_seven : AN 13 wbit = 7` — a matching explicit 7‑state witness, the path automaton of the colouring `0,1,2,3,4,4,4,4,4,4,4,5,6,0` of the 14 positions.
- `AneVsAn.Bin.ANe_lt_AN : ANe 13 wbit < AN 13 wbit` — the separation, combining `ANe = 6` (proved earlier) with `AN = 7`.

**How the lower bound is proved.** The argument mirrors the earlier `A_Ne ≥ 6` proof, with exact acceptance replaced by unique acceptance.
1. *Reduction to path automata.* From the accepting run of a hypothetical ≤6‑state NFA, deleting all unused transitions and keeping only the last state as accepting can only remove accepting paths, so unique acceptance is inherited. Everything reduces to colourings `c : ℕ → Fin 6` of the 14 positions (`uniqueSizes_ge_seven`).
2. *Deviation sets.* `Dset c t` is the set of states reachable at time `t` by a path/word pair that has already deviated from `(w, c)` — a wrong letter or a wrong state. Uniqueness fails **iff** `c 13 ∈ Dset c 13`, and already fails as soon as `c t ∈ Dset c t` for some `t ≤ 13` (complete the deviating path along the colouring). Both directions are proved (`not_uniqueCol_of_Dset`, `uniqueCol_of_not_Dset`), and `Dcomp` computes these sets with proved soundness and completeness.
3. *Pruned depth‑first search.* `dfsU` extends a colouring position by position, recomputing the deviation set from the transitions known so far and cutting a branch as soon as the criterion fires — sound because a partial transition set only under‑approximates. `dfsU_sound` turns a successful search into "no 6‑colouring works". Relabelling states (`uniqueCol_relabel`, valid since renaming states does not change unique acceptance) lets the search fix the start state, cutting it by a factor 6; the pruning collapses the space to about 3·10⁵ nodes.

**On the machine computations.** The 6‑state search `searchU_ok` is too large for kernel reduction, so it is discharged as a compiled computation; consequently `AN_ge_seven` (and hence `AN_eq_seven`, `ANe_lt_AN`) depends on Lean's standard compiler‑trust axioms in addition to the usual ones — exactly as the companion bound `ANe_ge_six` already did. The small computation behind the upper bound (`c7_not_mem`) is discharged by plain `decide`, so `AN_le_seven` is fully kernel‑checked and uses only `propext`, `Classical.choice`, `Quot.sound`.

All work is committed.

# Summary of changes for run 98938220-3b62-4d21-bbcb-7a18d13640f6
**Result: `A_Ne(1101000000100) ≥ 6` is proved formally — and in fact `A_Ne = 6` exactly.**

All new material is in `RequestProject/BinaryLower.lean` (no `sorry`), and the project builds cleanly. Every declaration carries a docstring; where a step mirrors the attached paper, the docstring names the corresponding informal statement.

**Statements proved**
- `AneVsAn.Bin.ANe_ge_six : 6 ≤ ANe 13 wbit` — the requested lower bound: every NFA that exactly accepts the length‑13 binary word `1101000000100` has at least 6 states.
- `AneVsAn.Bin.ANe_le_six` and `AneVsAn.Bin.ANe_eq_six : ANe 13 wbit = 6` — a matching explicit 6‑state witness, so the complexity is exactly 6.

**Why the decision procedure is feasible.** A naive enumeration of 5‑state NFAs (or even of all 5‑colourings of the 14 positions, about 6·10⁹) is hopeless, so the proof first reduces and then prunes:
1. *Reduction to path automata.* From an accepting run of a hypothetical ≤5‑state NFA, discarding all unused transitions and keeping only the last state as accepting shrinks the language, so exact acceptance is inherited. Everything therefore reduces to colourings `c : ℕ → Fin 5` of the 14 positions (`exactSizes_ge_six`).
2. *A two‑set subset construction.* `Gset c t` (states reachable at time `t` by the correct prefix) and `Uset c t` (states reachable at time `t` by any other word) are enough: exactness fails **iff** `c 13 ∈ Uset c 13`, and more usefully, it already fails as soon as `c t ∈ Uset c t` for some `t` (complete the run along the colouring itself). Both directions are proved (`not_exactCol_of_Uset`, `exactCol_of_not_Uset`), and `guIter` computes these sets with proved soundness and completeness.
3. *Pruned depth‑first search.* `dfs` extends a colouring position by position, recomputing `Gset`/`Uset` from the transitions known so far and cutting a branch as soon as the criterion in 2 fires — sound because a partial transition set only under‑approximates. `dfs_sound` turns a successful search into "no 5‑colouring works". The pruning collapses the space to roughly 10⁵ nodes, and the search itself (`search_ok`) runs in seconds.

**On `decide` vs `native_decide`.** The 5‑state search `search_ok` is still too large for kernel reduction (a kernel `decide` did not finish in 25 minutes), so it uses `native_decide`; consequently `ANe_ge_six` depends on Lean's standard compiler‑trust axioms in addition to the usual ones. The small computation behind the upper bound (`c6_not_mem`) is discharged by plain `decide`, so `ANe_le_six` is fully kernel‑checked and uses only `propext`, `Classical.choice`, `Quot.sound`.

**One supporting change.** The definitions of runs, exact/unique acceptance and the complexities `ANe`/`AN` in `RequestProject/Defs.lean` were generalized from the paper's alphabet to an arbitrary alphabet `Λ`, so the binary word is treated over `Bool` (`true = 1`) rather than being encoded into the paper's letters; the existing development for Theorem 1.2 is unaffected and still builds (its previously recorded open leaves are untouched).

The 6‑state witness, for reference, is the path automaton of the colouring `0,1,2,3,4,5,4,5,5,4,1,2,3,0` of the 14 positions.

# Summary of changes for run 9e7a9e8f-c0e8-488e-beb6-5831978d331f
Yes — the single remaining `sorry` has been replaced by a skeleton, and one of the resulting pieces has been proved outright, so nine leaf `sorry`s remain. The project builds cleanly.

**What changed**

- `RequestProject/WalkEndgame.lean` (new): the structure `GammaData`, which packages the conclusions of Lemma 5.3 (`lem:gamma`) — the cycle γ, its stretch, and the bookkeeping quantities ℓ, t, r_off, d₀, x₁, b₁, s₀ — together with the leaf statements of Sections 5.2–6 and the fully proved assembly.
- `RequestProject/WalkBase.lean` (new): the base cases k ∈ {3,6,9,12,15}, isolated as one finite search, plus the (proved) recolouring lemma reducing an arbitrary walk with ≤ k+5 states to a colouring by `Fin (k+5)`.
- `RequestProject/WalkMain.lean`: `walk_card_lower` no longer contains a `sorry` of its own; it is now derived from the leaves via the assembly lemmas, following the "Conclusion of the proof" of Section 6 of the source.
- `REMAINING_SORRIES.md`: a table listing the nine leaves, which is which, and what is already available to prove them. Every declaration carries a docstring naming the corresponding informal result.

**Newly proved this session (previously part of the single `sorry`)**

- `exists_maximal_Stretch` (with helper `no_repeat_in_period`): the maximality half of Step 1 of `lem:gamma` — the stretch can be chosen so that every visit of a γ-state lies inside it.
- `shapes` (Corollary 6.2, `cor:shapes`): the arithmetic leaving only the three shapes ℓ = 1, ℓ = 2 (clean/bridge) and ℓ = 4, including the exclusion of ℓ = 3, the one place where k ≡ 0 (mod 3) is used.
- `bridge_single_parity` (b₁ ≡ s₀ mod 2), `exists_GammaData`, `no_small_walk_large`, `walk_relabel`, `walk_card_lower_base` and `walk_card_lower` itself.

**The nine remaining `sorry`s**

Genuinely requiring a proof (all in `RequestProject/WalkEndgame.lean`; each is about an arbitrary walk for an arbitrary k ≥ 18, so none is a finite check):
1. `gamma_offCycle_count` — Steps 2, 4, 5 of `lem:gamma` (`eq:dzero`);
2. `aligned_nonempty` — Lemma 5.11 (`lem:Inonempty`);
3. `bridgeCount_eq_zero_of_ell_one` — Lemma 5.13 (`lem:bridgeparity`), case ℓ = 1;
4. `bridgeCount_le_one_of_ell_two` — Lemma 5.14(a) (`lem:twoodd`);
5.–8. `ell_one_impossible`, `ell_four_impossible`, `ell_two_clean_impossible`, `ell_two_bridge_impossible` — Propositions 6.3, 6.5, 6.7, 6.8.

Decidable in principle, being a finite search:
9. `base_search` (in `RequestProject/WalkBase.lean`) — for k ∈ {3,6,9,12,15}, no colouring of the 3k+8 positions of z_k by k+5 states is a uniquely accepting walk. This is exactly the exhaustive machine search of Section 7 of the source that the original task allowed to remain unproved: it concerns the finitely many colourings {0,…,3k+7} → Fin (k+5), and unique acceptance for each is decided by inspecting the finitely many paths of length n in the resulting walk graph. (As written it is not literally an instance of Lean's `Decidable`, since a colouring is a function on all of ℕ and unique acceptance quantifies over word/path pairs, but both depend only on the restrictions to {0,…,n}.)

One caveat worth stating plainly: the leaves 1–8 sit inside a proof by contradiction, so their ambient hypotheses are ultimately unsatisfiable; the decomposition is a faithful road map of the source's argument rather than a logical simplification of it. `#print axioms` confirms that the two upper bounds and the newly proved lemmas use only the standard axioms, and that the main theorem's only extra dependency is `sorryAx`, coming from the nine leaves. All work is committed and pushed.

# Summary of changes for run a04495b8-a6ab-49ab-b6a7-a9f69ed1f4c3
## What I did this session

I continued the Lean 4 formalization of Theorem 1.2 of `anevsanseparationv4.tex` ("Exact beats unique infinitely often"). Every declaration carries a docstring naming the corresponding informal result in the source (`lem:narrow`, `lem:wide`, `lem:positions`, `lem:bridgeparity`, `lem:dichotomy`, …). The project builds cleanly and contains exactly **one** `sorry`, in `AneVsAn.walk_card_lower` (`RequestProject/WalkMain.lean`).

### New this session

- **`RequestProject/Seg.lean`** — added `repit_zero`, `repit_at_period` (evaluation of repeated closed paths).
- **`RequestProject/WalkTools.lean`** — `shift_classification` (`cor:shifts`) and `narrow_lengths_distinct` (two distinct narrow chords have distinct lengths).
- **`RequestProject/WalkSurgery.lean`** — the whole of Section 5.3:
  - `c_edge_moves`, the reusable "moved `c`-edge" contradiction;
  - `narrow_prefix_skip`, `narrow_tail_skip`, `narrow_prefix_insert`, `narrow_tail_insert` (`lem:narrow`(a),(b));
  - `narrow_prefix_pair`, `narrow_tail_pair`, `narrow_mixed_pair` (`lem:narrow`(c),(d), all three chord configurations);
  - `wide_chord_fold` (`lem:wide`(ii)), `foldloop_lt`/`foldloop_gt` (`cor:foldloop`), `lasso_u1`/`lasso_u2` (`lem:lasso`);
  - `double_passage` (`lem:dichotomy`);
  - the spin-adjustment tool `Stretch.slen` / `Stretch.spanSeg`, and `exists_Stretch`, which assembles Step 1 of `lem:gamma` into a `Stretch` object with `ℓ ≤ 4` and `t ≥ 4`.
- **`RequestProject/WalkPositions.lean`** (new) — `wide_chords_nested` (`lem:wide`(i)) and all six parts of the position constraints `lem:positions`.
- **`RequestProject/WalkBridges.lean`** (new) — the four bridge surgeries behind `lem:bridgeparity`: `bridge_prefix`, `bridge_tail`, `bridge_wide_prefix`, `bridge_wide_tail`.

### State of the formalization

Proved and `sorry`-free: the two upper bounds (`ANe_upper`, Proposition 3.2; `AN_upper`, Proposition 3.3), the master lemmas of Section 4 (rotation, pair table, shift classification, square structure, two-visit, aligned block, crossing), the counting identities and budget inequality of Section 5.1, Step 1 of the cycle lemma, and every surgery of Sections 5.3–5.5 and 6.1.

Still open, and the content of the single remaining `sorry`: the combinatorial bookkeeping that glues the surgeries together — Steps 2–5 of the cycle lemma (`lem:gamma`), `lem:Inonempty`, `lem:counts`, `lem:twoodd`, `cor:shapes`, and the endgame case analysis (`prop:ell1`, `prop:ell4`, `prop:ell2clean`, `prop:ell2bridge`) — together with the base cases `k ∈ {3,6,9,12,15}`, which the source settles by exhaustive machine search (and which you allowed to remain unproved). Because of this, `AN_lower` and `main_theorem` are stated in full and correctly reduced, but their proofs still depend on that `sorry`; I have recorded this honestly in the Properties table and in the module docstring of `RequestProject/WalkMain.lean`, which lists exactly what is done and what is not.

All work is committed and pushed.