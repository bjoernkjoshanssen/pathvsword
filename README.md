# Exact and unique nondeterministic automatic complexity

This Lean 4.28.0 project studies the separation between exact nondeterministic
automatic complexity `ANe` and unique nondeterministic automatic complexity `AN`.

## Infinitely many binary separations

The binary development proves

```lean
theorem infinite_binary_separations :
    Set.Infinite {w : List Bool | Separates w}
```

Here `Separates w` means `ANe w < AN w`, using the original complexity definitions
and the finite word's length. The theorem lives in the namespace
`AneVsAn.BinarySeparation` in
[`BinarySeparationInfinitude.lean`](RequestProject/BinarySeparationInfinitude.lean).

The proof gives a separating word of length `3 * 2^m + 7` for every `m ≥ 64`.
It also proves that the set of separating lengths is infinite, so the words
remain distinct up to alphabet renaming.

Read [the proof guide](BINARY_SEPARATION_PROOF.md) for the construction, finite
counting argument, simplifications, and module map.

To check the result and its transitive axiom dependencies:

```sh
lake exe cache get
lake build RequestProject.BinarySeparationAudit
```

The audit permits only `propext`, `Classical.choice`, and `Quot.sound`; it fails
on `sorryAx`, custom axioms, or native evaluation axioms. The binary result is
independent of the older arbitrary-alphabet development's finite-search
placeholder documented in [REMAINING_SORRIES.md](REMAINING_SORRIES.md).

Run `lake build` to check the whole project. GitHub Actions runs this build,
including the binary axiom audit, on pushes and pull requests.

## Earlier development

The existing arbitrary-alphabet theorem is in
[`Main.lean`](RequestProject/Main.lean).

This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```
