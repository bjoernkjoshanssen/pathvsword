import RequestProject.WalkPositions

/-!
# Bridge surgeries (Section 5.5 of `anevsanseparationv4.tex`)

A *bridge* is a state with one visit at a run time `τ` and one visit at a non-run time.
Its chord is `(j,τ)` (prefix bridge, `j ≤ k-1`) or `(τ, 2k+6+j')` (tail bridge).
Lemma 5.13 (Bridge parity, `lem:bridgeparity`) shows that for `ℓ ≤ 2` the length of a
bridge chord cannot be divisible by `ℓ`; its proof distinguishes *early*, *late* and
*wide* bridge chords.  This file provides the four surgeries used there:

* `bridge_prefix` — the skip of a prefix bridge chord (the *early* case, and in fact any
  prefix bridge whose chord is short enough);
* `bridge_tail` — the corresponding surgery for a tail bridge chord;
* `bridge_wide_prefix`, `bridge_wide_tail` — the *wide* cases, where the chord contains
  the stretch and the path traverses the stretch twice (spin adjustment in two
  traversals).
-/

namespace AneVsAn

set_option autoImplicit false

section

variable {k : ℕ} {S : Type} {c : ℕ → S}

/-- **Lemma 5.13 (Bridge parity, `lem:bridgeparity`)**, prefix bridges.  For a prefix
bridge chord `(j,τ)` the path `W[0,τ] W[j,k] R⟨m-L⟩ W[2k+5,n]` (`L = τ-j`) is a walk of
the walk graph from `c₀` to `c_n`; if it has length `n` it is a second accepting path,
since it reads `a_{j+1}` at the position `τ`, where `W` reads `b` or `c`. -/
theorem bridge_prefix (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) {j tau u : ℕ} (hjk : j < k) (htau : k ≤ tau)
    (htau2 : tau ≤ 2 * k + 5) (hchord : c j = c tau)
    (hlen : tau + ((k - j) + ((Str.d0 + u * Str.ell) + (k + 2))) = 3 * k + 7) : False := by
  obtain ⟨τr, hτr⟩ := Str.runSeg hk u
  have s0 : Seg k c (c 0) (c tau) tau (fun t => 0 + t) := by
    have h := segW (k := k) c (show (0 : ℕ) ≤ tau by omega) (by omega)
    simpa using h
  rw [← hchord] at s0
  have s1 : Seg k c (c j) (c k) (k - j) (fun t => j + t) := segW c (by omega) (by omega)
  have s2 : Seg k c (c (2 * k + 5)) (c (3 * k + 7)) (k + 2) (fun t => 2 * k + 5 + t) := by
    have h := segW (k := k) c (show 2 * k + 5 ≤ 3 * k + 7 by omega) (by omega)
    rw [show 3 * k + 7 - (2 * k + 5) = k + 2 by omega] at h; exact h
  have hall := seg_cat s0 (seg_cat s1 (seg_cat hτr s2))
  rw [hlen] at hall
  refine no_second_path hk huaw hall (j := tau) (by omega) ?_
  have hτ : cat tau (fun t => 0 + t)
      (cat (k - j) (fun t => j + t)
        (cat (Str.d0 + u * Str.ell) τr (fun t => 2 * k + 5 + t))) tau = j := by
    rw [cat_ge (by omega), Nat.sub_self, cat_lt (by omega)]
    omega
  rw [hτ, zw_a hjk]
  rcases (by omega : tau < 2 * k + 5 ∨ tau = 2 * k + 5) with h | h
  · rw [zw_b htau h]; simp
  · rw [zw_c h]; simp

/-- **Lemma 5.13 (Bridge parity, `lem:bridgeparity`)**, tail bridges.  For a tail bridge
chord `(τ, 2k+6+j')` the path
`W[0,k] R⟨m-L⟩ W[2k+5,2k+6+j'] W[τ,2k+5] W[2k+5,n]` enters the tail through the bridge;
its `c`-edge has moved, so it differs from `W`. -/
theorem bridge_tail (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) {jp tau u : ℕ} (hjp : jp ≤ k + 1)
    (htau2 : tau ≤ 2 * k + 5) (hchord : c tau = c (2 * k + 6 + jp))
    (hlen : k + (Str.d0 + u * Str.ell) +
      ((2 * k + 6 + jp - (2 * k + 5)) + ((2 * k + 5 - tau) + (k + 2))) = 3 * k + 7)
    (hne : Str.d0 + u * Str.ell ≠ k + 5) : False := by
  have q1 : Seg k c (c (2 * k + 5)) (c (2 * k + 6 + jp)) (2 * k + 6 + jp - (2 * k + 5))
      (fun t => 2 * k + 5 + t) := segW c (by omega) (by omega)
  rw [← hchord] at q1
  have q2 : Seg k c (c tau) (c (2 * k + 5)) (2 * k + 5 - tau) (fun t => tau + t) :=
    segW c (by omega) (by omega)
  have q3 : Seg k c (c (2 * k + 5)) (c (3 * k + 7)) (k + 2) (fun t => 2 * k + 5 + t) := by
    have h := segW (k := k) c (show 2 * k + 5 ≤ 3 * k + 7 by omega) (by omega)
    rw [show 3 * k + 7 - (2 * k + 5) = k + 2 by omega] at h; exact h
  exact c_edge_moves hk huaw Str u _ (seg_cat q1 (seg_cat q2 q3)) (by omega)
    (by rw [cat_lt (show (0 : ℕ) < 2 * k + 6 + jp - (2 * k + 5) by omega)]) (by omega) hne

/-- **Lemma 5.13 (Bridge parity, `lem:bridgeparity`)**, wide prefix bridges.  Here the
chord `(j,τ)` contains the stretch, and the path `W[0,τ] W[j,τ] W[τ,n]` traverses the
stretch twice; spin adjustment in the two traversals restores the length `n`.  The path
reads `a_{j+1}` at the junction, where `W` reads `b`. -/
theorem bridge_wide_prefix (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) {j tau u : ℕ} (hjk : j < k) (htauq : Str.q ≤ tau)
    (htau2 : tau ≤ 2 * k + 5) (hchord : c j = c tau)
    (hlen : k + (Str.slen k tau 0 + ((k - j) + (Str.slen k tau u + (3 * k + 7 - tau))))
      = 3 * k + 7) : False := by
  have hs : Str.slen k tau 0 ≤ Str.d0 := by
    simp only [Stretch.slen, Stretch.d0]; omega
  have hd := Str.d0_le
  have s0 : Seg k c (c 0) (c k) k (fun t => 0 + t) := by
    have h := segW (k := k) c (show (0 : ℕ) ≤ k by omega) (by omega)
    simpa using h
  obtain ⟨τA, hA⟩ := Str.spanSeg Str.hp htauq (by omega) 0
  rw [← hchord] at hA
  have s1 : Seg k c (c j) (c k) (k - j) (fun t => j + t) := segW c (by omega) (by omega)
  obtain ⟨τB, hB⟩ := Str.spanSeg Str.hp htauq (by omega) u
  have s2 : Seg k c (c tau) (c (3 * k + 7)) (3 * k + 7 - tau) (fun t => tau + t) :=
    segW c (by omega) (by omega)
  have hall := seg_cat s0 (seg_cat hA (seg_cat s1 (seg_cat hB s2)))
  rw [hlen] at hall
  refine no_second_path hk huaw hall (j := k + Str.slen k tau 0) (by omega) ?_
  have hτ : cat k (fun t => 0 + t)
      (cat (Str.slen k tau 0) τA
        (cat (k - j) (fun t => j + t)
          (cat (Str.slen k tau u) τB (fun t => tau + t)))) (k + Str.slen k tau 0) = j := by
    rw [cat_ge (by omega), show k + Str.slen k tau 0 - k = Str.slen k tau 0 by omega,
      cat_ge (by omega), Nat.sub_self, cat_lt (by omega)]
    omega
  rw [hτ, zw_a hjk, zw_b (by omega) (by omega)]
  simp

/-- **Lemma 5.13 (Bridge parity, `lem:bridgeparity`)**, wide tail bridges.  The chord
`(τ, 2k+6+j')` contains the stretch; the path
`W[0,2k+6+j'] W[τ,2k+6+j'] W[2k+6+j',n]` traverses it twice and has two `c`-edges. -/
theorem bridge_wide_tail (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) {jp tau u u2 : ℕ} (hjp : jp ≤ k + 1) (htaup : tau ≤ Str.p)
    (hchord : c tau = c (2 * k + 6 + jp))
    (hlen : k + (Str.d0 + u * Str.ell) +
      ((2 * k + 6 + jp - (2 * k + 5)) + (Str.slen tau (2 * k + 5) u2 +
        ((2 * k + 6 + jp - (2 * k + 5)) + (3 * k + 7 - (2 * k + 6 + jp))))) = 3 * k + 7)
    (hne : Str.d0 + u * Str.ell ≠ k + 5) : False := by
  have q1 : Seg k c (c (2 * k + 5)) (c (2 * k + 6 + jp)) (2 * k + 6 + jp - (2 * k + 5))
      (fun t => 2 * k + 5 + t) := segW c (by omega) (by omega)
  rw [← hchord] at q1
  obtain ⟨τB, hB⟩ := Str.spanSeg htaup Str.hq (by omega) u2
  have q2 : Seg k c (c (2 * k + 5)) (c (2 * k + 6 + jp)) (2 * k + 6 + jp - (2 * k + 5))
      (fun t => 2 * k + 5 + t) := segW c (by omega) (by omega)
  have q3 : Seg k c (c (2 * k + 6 + jp)) (c (3 * k + 7)) (3 * k + 7 - (2 * k + 6 + jp))
      (fun t => 2 * k + 6 + jp + t) := segW c (by omega) (by omega)
  exact c_edge_moves hk huaw Str u _ (seg_cat q1 (seg_cat hB (seg_cat q2 q3))) (by omega)
    (by rw [cat_lt (show (0 : ℕ) < 2 * k + 6 + jp - (2 * k + 5) by omega)]) (by omega) hne

end

end AneVsAn
