# Infinitely many binary separations

This development proves that infinitely many finite binary words satisfy

\[
A_{Ne}(w)<A_N(w).
\]

The alphabet is `Bool` throughout the new construction. The final statement is
about `List Bool`, and the proof produces separating words of unbounded lengths.
Consequently it also supplies infinitely many nonisomorphic words: an alphabet
renaming preserves length.

The development uses the repository's existing definitions of `ExactlyAccepts`,
`UniquelyAccepts`, `ANe`, and `AN`. It keeps Lean and Mathlib at version **4.28.0**.
The only change to `Defs.lean` is its import list; the complexity definitions have
not changed.

## Statements and scope

The public statements are in
[`RequestProject/BinarySeparationInfinitude.lean`](RequestProject/BinarySeparationInfinitude.lean),
in the namespace `AneVsAn.BinarySeparation`:

| Theorem | Content |
| --- | --- |
| `separation_at_exponential_lengths` | Separating binary words exist at each length `3 * 2^m + 7`, for `m ≥ 64`. |
| `binary_separations_unbounded_lengths` | A separating binary word exists beyond every prescribed length bound. |
| `infinite_binary_separations` | The set of separating finite binary words is infinite. |
| `infinite_binary_separation_lengths` | The set of lengths of separating binary words is infinite. |

The conditional result in
[`RequestProject/BinarySeparationMain.lean`](RequestProject/BinarySeparationMain.lean)
is deliberately tailored to infinitude. It proves

\[
A_{Ne}(x_u)\le L+2<L+3\le A_N(x_u)
\]

under the following hypotheses:

1. `L ≥ 6` and `L % 4 = 2`;
2. `3 ≤ B ≤ L - 2`;
3. the seed is `BGood`;
4. `2 * (B - 1) * (B^3 + 4) < 4 * (L + 2)`;
5. the seed begins with `001`: `u 1 = false`, `u 2 = false`, `u 3 = true`.

Its three main interfaces are `binary_walk_card_lower`, `binary_AN_lower`, and
`binary_family_separation`. The proof does not require the sharper unique upper
bound `A_N(x_u) ≤ L + 3`, the finite witness tables, or a theorem covering every
admissible small length.

## The binary family

For a seed of length `L - 2`, use

\[
x_u=0\,u\,1\,0^{L+1}\,1\,u\,0,
\qquad |x_u|=3L+1.
\]

`word L u` represents the word as a function `ℕ → Bool`; only values below
`3 * L + 1` matter. Seed positions use the manuscript's indices `1, …, L - 2`.
`GenericComplexity.lean` proves that the complexities are unchanged when these
relevant positions agree, then transfers the result to a finite list.

`HasPeriod x i j p` means that the occurrence `[i,j)` has period `p`.
`BGood L B u` says that any periodic occurrence of length at least `2p`, outside
the designated central run, has length less than `p + B`. The run's **letter**
positions are `L, …, 2L`; the corresponding **state times** are `L, …, 2L + 1`.
These different endpoint conventions are explicit in the definitions.

## Exact upper bound

`BinarySeparationUpper.lean` defines an NFA with the chain states
`0, …, L - 1` and two zero-gadget states `L, L + 1`. It has one start state, one
final state, and no epsilon transitions, exactly as in `Defs.lean`.

Every accepting run starts with the chain and ends with the edge to state `0`.
An intervening return to the last chain state has length `L + z`, where `z = 0`
or `z ≥ 2`. At total length `3L + 1`, the intervening returns have total length
`2L + 1`. Two returns would require their extra lengths to sum to `1`, which is
impossible. The one possible return traverses the zero gadget for `L + 1` steps
and spells exactly the displayed word.

The formal proof gives both an explicit accepting run and a proof that every
accepting run of this length spells `word L u`. `exact_size` therefore gives a
member of the original set `ExactSizes`; `ANe_le` gives the complexity bound.
The same module proves `uniqueSizes_nonempty` by a chain automaton. This supplies
the nonemptiness needed when taking the infimum defining `AN`.

## The unique lower bound

The proof works with uniquely accepting walks in their own transition graphs.
`GenericWalk.lean`, `GenericSegments.lean`, and the related generic modules give
the word-independent surgery facts used below. In particular, a second path of
the same length and with the same endpoints must have the same edges and states.
This yields rotation, arithmetic progressions of visits, exchange of closed
paths, and restrictions on loops.

### A coarse surplus estimate

`BinarySeparationOuter.lean` proves that every state with an outside visit has
at most two visits **in total**, including its visits inside the run.

For contradiction, suppose an outer state has at least three visits. Goodness
bounds its period by `B - 1`. All repeated outer states with the same period
have first visits in an interval shorter than that period. Thus there are at
most `B` such states for each of fewer than `B` periods, and each state has at
most `B` excess visits beyond its first two. The total excess is at most `B^3`.

An exchange argument also shows that a state confined to the run has at most
the chosen outer state's period many visits. Otherwise an outer first-return
cycle can be exchanged with a sufficiently long central chord. Its edges would
all occur in the zero run, forcing the entire outer periodic stretch to be zero.
The stretch crosses a delimiter labeled `1`, which is impossible.

Combining these bounds with the `3L + 2` state times and the assumed state budget
`L + 2` contradicts the numerical hypothesis above. This proof treats all
positive periods uniformly, including periods one and two.

This is a simplification of the supplied manuscript's sharper surplus estimate.
The weaker cubic bound is sufficient for the chosen infinite sequence and avoids
a separate residue-by-residue count and separate low-period cases.

### The remaining run configurations

`BinarySeparationCount.lean` and `BinarySeparationConfigurations.lean` reduce a
putative small unique walk to either a long loop confined to the run or a
confined alternating two-cycle. The long loop has one of four possible endpoint
pairs.

The loop modules exclude these possibilities by explicit path surgeries,
ordered-state arguments, and the fixed seed prefix. A loop of length `L`
forces the whole seed to be zero, contradicting goodness; that argument is
invariant under reversal and handles both orientations.

For the alternating two-cycle, `BinarySeparationPairing.lean` obtains a bijection
between the `L` state times on each side. The exchange of two same-side chords
with central rounds excludes a pair entirely within each side. Consequently
every outer state appears once on each side.

Normalize this matching to a permutation `f` of `0, …, L - 1`. Crossing surgery
shows that any increasing pair of values has equal displacement. Hence the
permutation consists of increasing intervals whose images occur in reverse
order. A closed path from two adjacent intervals must have odd length greater
than `L/2`. Four intervals are already impossible, because the first two and
the next two would each contain more than `L/2` positions.

One interval contradicts the fixed prefix. Two intervals would make `L` odd.
With three intervals, tripling a shortened enclosing path gives a lower bound
on the last interval's cross-pair span. Together with the adjacent-interval
cycle bound, this forces `L = 0 mod 4`, contradicting `L = 2 mod 4`.

`BinarySeparationLayered.lean` constructs at most four successive permutation
tails directly. It does not need a list of all maximal intervals. The formal
endgame also needs only the triple-path span estimate, so it omits the
manuscript's additional estimate for even spans.

## Existence by finite counting

The existence proof uses a finite space of assignments to `Fin (L - 2)`;
it does not use a probability library or an unverified random search.

Consider a bad factor `[i,j)` of period `p`. There are `j - i - p` comparison
equations `x_t = x_(t+p)`, and badness says that this number is at least `B`.
If any assignment satisfies these equations, at most three equations compare
two fixed bits. Their comparison positions are among

\[
t=0,\qquad t=L-1,\qquad t+p=3L.
\]

Indeed, a comparison between two central zero-run positions, in a factor that
crosses a run boundary, would force another comparison between a delimiter `1`
and a run `0`. Every other equation involves a seed variable. The period bounds
give `0 < p < 2L + 1`, so none of these variable equations is the tautological
comparison between the two occurrences of the same seed bit.

There are therefore at least `B - 3` nontrivial equations. Each seed variable
occurs in at most four equations, and each equation uses at most two variables.
The generic finite-set lemma `exists_disjoint_supports` selects a subfamily of
pairwise variable-disjoint equations with at least one eighth as many members.
For `r` selected equations, restriction to the nonpivot variables is injective
on satisfying assignments. Thus at most `2^(L - 2 - r)` assignments satisfy a
particular bad factor.

The union is taken over **all** endpoint/period triples. There are at most
`(3L + 2)^3` of these. This deliberately coarse union replaces the manuscript's
minimal-window extraction, three window types, and geometric-series estimate.

The fixed prefix `001` leaves exactly `L - 5` free seed bits. An explicit
injective assignment map installs the three fixed bits. A bad factor still has
at most the same number of assignments in this smaller space, so it suffices
that

\[
(3L+2)^3<2^{r-3},\qquad 8r+3\le B,\qquad r\le L-2.
\]

These are the hypotheses of `exists_good_with_prefix_of_large_space`.

## The infinite sequence

For every `m ≥ 64`, take

\[
L_m=2^m+2,\qquad B_m=64m+8,\qquad r_m=8m.
\]

`BinarySeparationNumerics.lean` proves all the needed inequalities by natural
number arithmetic and induction. In particular,

\[
B_m^4<2^m,
\qquad
(3L_m+2)^3<2^{8m-3},
\qquad
L_m\equiv2\pmod4.
\]

Consequently `exists_good_with_prefix_on_subsequence` supplies an admissible
seed for each `m`. Applying the conditional separation theorem gives a binary
separation of length `3 * 2^m + 7`. These lengths are strictly increasing and
unbounded.

The chosen sequence `separatingWord : ℕ → List Bool` is indexed from zero, so
`separatingWord m` has length `3 * 2^(m + 64) + 7`. Its definition uses classical
choice from the proved existence theorem. `separatingWord_lengths_strictMono`
and `separatingWord_injective` then give the two final infinitude statements.

The constants are intentionally generous. Optimizing the threshold or proving
the manuscript's stronger coverage of small lengths is separate from the
infinitude statement formalized here.

## Module and validation guide

| Modules | Role |
| --- | --- |
| `Defs`, `ProofImports` | Original complexity definitions and focused Mathlib imports. |
| `GenericWalk`, `GenericSegments`, `GenericWalkTools`, `GenericVisitProgression`, `GenericLoops`, `GenericReversal` | Generic unique-walk and surgery infrastructure. |
| `BinarySeparationDefs`, `BinarySeparationUpper` | Binary word, goodness, exact upper bound, and nonempty unique-size sets. |
| `BinarySeparationOuter`, `BinarySeparationCount`, `BinarySeparationConfigurations` | Outer visit bound and reduction of the run's state structure. |
| `BinarySeparationLoopTools`, `BinarySeparationPermutation`, `BinarySeparationLoopA0`, `BinarySeparationLoopA2`, `BinarySeparationLoopLengthL`, `BinarySeparationReversal` | Long-loop endgames and reversal. |
| `BinarySeparationPairing`, `BinarySeparationLayered`, `BinarySeparationTwoCycleTools`, `BinarySeparationTwoCycleEndgame` | Confined two-cycle endgame. |
| `BinarySeparationCounting`, `BinarySeparationExistence`, `BinarySeparationNumerics` | Finite counting, fixed-prefix existence, and parameter bounds. |
| `BinarySeparationMain`, `GenericComplexity`, `BinarySeparationInfinitude` | Complexity lower bound, finite-list transfer, and infinitude. |
| `BinarySeparationAudit` | Failing build gate for the transitive axiom dependencies of the five public results. |

The final target can be built independently of the older separation theorem:

```sh
lake build RequestProject.BinarySeparationInfinitude
```

The checked axiom gate is:

```sh
lake build RequestProject.BinarySeparationAudit
```

This target has passed. It examines the transitive dependencies of
`binary_family_separation`, `separation_at_exponential_lengths`,
`binary_separations_unbounded_lengths`, `infinite_binary_separations`, and
`infinite_binary_separation_lengths`. Compilation fails if any of these results
depends on an axiom outside the explicit allowlist `propext`, `Classical.choice`,
and `Quot.sound`. This includes a failure for `sorryAx`, custom axioms, or native
evaluation axioms, even when introduced through a dependency.

For a printed inspection of the final statements:

```lean
import RequestProject.BinarySeparationInfinitude

#print axioms AneVsAn.BinarySeparation.infinite_binary_separations
#print axioms AneVsAn.BinarySeparation.infinite_binary_separation_lengths
```

The new proofs use no `sorry`, additional axioms, or `native_decide` shortcuts.
Their ordinary logical dependencies are `propext`, `Classical.choice`, and
`Quot.sound`. In particular, `Classical.choice` selects seeds from the finite
existence proof; it does not stand for a computational witness table or an
assumed separation theorem.
