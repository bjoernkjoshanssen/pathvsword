import RequestProject.WalkBridges
import RequestProject.WalkBlockCount

/-!
# Bridge parity (Lemma 5.13, `lem:bridgeparity`) and the case `ℓ = 1`

This file formalizes Section 5.5 (`sec:bridges`) of `ane-vs-an-separation-v4_1.tex`.

A *bridge* is a state with exactly one run visit `τ` and exactly one non-run visit; its
chord is `(j, τ)` (prefix bridge, `j ≤ k-1`) or `(τ, 2k+6+j')` (tail bridge).  Lemma 5.13
(`lem:bridgeparity`) shows that the length `L` of a bridge chord cannot be divisible by
`ℓ`; the proof distinguishes the *early*, *late* and *wide* positions of the chord
relative to the stretch `S`.  The four surgeries of `RequestProject/WalkBridges.lean` are
packaged here with the arithmetic that produces the required number of turns around `γ`:

* `bridge_short_prefix` — the early case (a prefix bridge with `L ≤ tℓ`);
* `bridge_short_tail` — the late case (a tail bridge with `L ≤ tℓ`);
* `bridge_span_prefix`, `bridge_span_tail` — the wide cases (`L ≤ 2tℓ`).

The main result is `no_bridge_of_ell_one`, the last sentence of Lemma 5.13: for `ℓ = 1`
every bridge chord has length divisible by `ℓ`, so there are no bridges, i.e. `b₁ = 0`.
The length bounds `eq:bridgelen` come from Lemma 5.12(c) (`lem:counts`), i.e. from
`blockCount_bound`.
-/

namespace AneVsAn

set_option autoImplicit false

section

variable {k : ℕ} {S : Type} {c : ℕ → S}

/-! ### The four surgeries of Lemma 5.13 (`lem:bridgeparity`) -/

/-- **Lemma 5.13 (`lem:bridgeparity`), early case.**  A prefix bridge chord `(j,τ)` of
length `L = τ-j` divisible by `ℓ` and with `L ≤ tℓ` is skipped by
`bridge_prefix` with `t - L/ℓ` turns around `γ`. -/
theorem bridge_short_prefix (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) {j tau : ℕ} (hjk : j < k) (htau : k ≤ tau)
    (htau2 : tau ≤ 2 * k + 5) (hchord : c j = c tau)
    (hdvd : Str.ell ∣ (tau - j)) (hle : tau - j ≤ Str.tt * Str.ell) : False := by
  obtain ⟨u₀, hu₀⟩ := hdvd
  have hu₀' : tau - j = u₀ * Str.ell := by rw [hu₀]; ring
  clear hu₀
  have hadd := Str.d0_add
  have hmul : (Str.tt - u₀) * Str.ell = Str.tt * Str.ell - u₀ * Str.ell := Nat.sub_mul _ _ _
  exact bridge_prefix hk huaw Str (u := Str.tt - u₀) hjk htau htau2 hchord (by omega)

/-- **Lemma 5.13 (`lem:bridgeparity`), late case.**  A tail bridge chord `(τ, 2k+6+j')`
of length `L` divisible by `ℓ` and with `L ≤ tℓ` is skipped by `bridge_tail`. -/
theorem bridge_short_tail (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) {jp tau : ℕ} (hjp : jp ≤ k + 1) (htau2 : tau ≤ 2 * k + 5)
    (hchord : c tau = c (2 * k + 6 + jp))
    (hdvd : Str.ell ∣ (2 * k + 6 + jp - tau))
    (hle : 2 * k + 6 + jp - tau ≤ Str.tt * Str.ell) : False := by
  obtain ⟨u₀, hu₀⟩ := hdvd
  have hu₀' : 2 * k + 6 + jp - tau = u₀ * Str.ell := by rw [hu₀]; ring
  clear hu₀
  have hadd := Str.d0_add
  have hmul : (Str.tt - u₀) * Str.ell = Str.tt * Str.ell - u₀ * Str.ell := Nat.sub_mul _ _ _
  exact bridge_tail hk huaw Str (u := Str.tt - u₀) hjp htau2 hchord (by omega) (by omega)

/-- **Lemma 5.13 (`lem:bridgeparity`), wide prefix bridge.**  The chord `(j,τ)` contains
the stretch; with `L ≤ 2tℓ` and `ℓ ∣ L` the spin adjustment in the two traversals of the
stretch restores the length `n`. -/
theorem bridge_span_prefix (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) {j tau : ℕ} (hjk : j < k) (htauq : Str.q ≤ tau)
    (htau2 : tau ≤ 2 * k + 5) (hchord : c j = c tau)
    (hdvd : Str.ell ∣ (tau - j)) (hle : tau - j ≤ 2 * (Str.tt * Str.ell)) : False := by
  obtain ⟨u₀, hu₀⟩ := hdvd
  have hu₀' : tau - j = u₀ * Str.ell := by rw [hu₀]; ring
  clear hu₀
  have hp := Str.hp
  have hq := Str.hq
  have hlenS := Str.hlen
  have hmul : (2 * Str.tt - u₀) * Str.ell = 2 * (Str.tt * Str.ell) - u₀ * Str.ell := by
    rw [Nat.sub_mul, Nat.mul_assoc]
  refine bridge_wide_prefix hk huaw Str (u := 2 * Str.tt - u₀) hjk htauq htau2 hchord ?_
  simp only [Stretch.slen, Nat.zero_mul]
  omega

/-- **Lemma 5.13 (`lem:bridgeparity`), wide tail bridge.**  The chord `(τ, 2k+6+j')`
contains the stretch, and the resulting path has two `c`-edges. -/
theorem bridge_span_tail (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) {jp tau : ℕ} (hjp : jp ≤ k + 1) (htaup : tau ≤ Str.p)
    (hchord : c tau = c (2 * k + 6 + jp))
    (hdvd : Str.ell ∣ (2 * k + 6 + jp - tau))
    (hle : 2 * k + 6 + jp - tau ≤ 2 * (Str.tt * Str.ell)) : False := by
  obtain ⟨u₀, hu₀⟩ := hdvd
  have hu₀' : 2 * k + 6 + jp - tau = u₀ * Str.ell := by rw [hu₀]; ring
  clear hu₀
  have hp := Str.hp
  have hq := Str.hq
  have hlenS := Str.hlen
  have hd0 := Str.d0_le
  have hmul : (2 * Str.tt - u₀) * Str.ell = 2 * (Str.tt * Str.ell) - u₀ * Str.ell := by
    rw [Nat.sub_mul, Nat.mul_assoc]
  refine bridge_wide_tail hk huaw Str (u := 0) (u2 := 2 * Str.tt - u₀) hjp htaup hchord ?_ ?_
  · simp only [Stretch.slen, Stretch.d0, Nat.zero_mul]
    omega
  · simp only [Nat.zero_mul]
    omega

end

section

variable {k : ℕ} {S : Type} [DecidableEq S] {c : ℕ → S}

/-! ### The case `ℓ = 1` of Lemma 5.13 (`lem:bridgeparity`) -/

/-- **Lemma 5.13 (Bridge parity, `lem:bridgeparity`), last sentence**: for `ℓ = 1` every
bridge chord has length divisible by `ℓ`, so a bridge would make `W` non uniquely
accepting; hence `b₁ = 0`.

The position of the non-run visit relative to the aligned block is Lemma 5.10(e)
(`lem:positions`), the length bounds `eq:bridgelen` come from Lemma 5.12(c)
(`lem:counts`), and the run visit `τ` lies outside the stretch by the maximality of the
stretch (Step 1 of Lemma 5.3, `lem:gamma`). -/
theorem no_bridge_of_ell_one (hk : 18 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) (hell : Str.ell = 1) (hd0le : Str.d0 + Str.ell ≤ 7)
    (hbs : bridgeCount k c + singleCount k c + 2 * Str.ell ≤ 8)
    (hmax : ∀ u, u ≤ 3 * k + 7 →
      (∃ x, Str.p ≤ x ∧ x < Str.p + Str.ell ∧ c x = c u) → Str.p ≤ u ∧ u ≤ Str.q) :
    bridgeCount k c = 0 := by
  classical
  by_contra hne0
  obtain ⟨y, hyf⟩ : ((onceSet k c).filter (fun s => (rvis k c s).card = 1)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [bridgeCount, h, Finset.card_empty] at hne0
    exact hne0 rfl
  rw [Finset.mem_filter, onceSet, Finset.mem_filter] at hyf
  obtain ⟨⟨-, hnv1⟩, hrv1⟩ := hyf
  obtain ⟨j, hjset⟩ := Finset.card_eq_one.1 hnv1
  obtain ⟨tau, htset⟩ := Finset.card_eq_one.1 hrv1
  have hjmem : j ∈ nvis k c y := by rw [hjset]; exact Finset.mem_singleton_self j
  have htmem : tau ∈ rvis k c y := by rw [htset]; exact Finset.mem_singleton_self tau
  rw [mem_nvis_iff] at hjmem
  obtain ⟨⟨hjn, hjr⟩, hcj⟩ := hjmem
  simp only [rvis, Finset.mem_filter, runTimes, Finset.mem_Icc] at htmem
  obtain ⟨⟨htau1, htau2⟩, hct⟩ := htmem
  -- the state `y` has no other non-run visit
  have honly : ∀ t, t < 3 * k + 8 → ¬ (k ≤ t ∧ t ≤ 2 * k + 5) → c t = y → t = j := by
    intro t h1 h2 h3
    have ht : t ∈ nvis k c y := mem_nvis_iff.2 ⟨⟨h1, h2⟩, h3⟩
    rw [hjset, Finset.mem_singleton] at ht
    exact ht
  -- the aligned block (Lemma 5.11, `lem:Inonempty`, and Lemma 4.6, `lem:block`)
  obtain ⟨i0, hi0k, halign0⟩ := exists_aligned_index hk huaw Str (by omega) hd0le hbs
  have hAne : (alignedSet k c).Nonempty := ⟨i0, mem_alignedSet.2 ⟨hi0k, halign0⟩⟩
  have hI := alignedSet_interval (by omega : 3 ≤ k) huaw hAne
  have hi1a := mem_alignedSet.1 (Finset.min'_mem (alignedSet k c) hAne)
  have hi2a := mem_alignedSet.1 (Finset.max'_mem (alignedSet k c) hAne)
  have hbc := blockCount_bound hk huaw Str hd0le hi0k halign0
  have hmx := alignedSet_card_le_max (k := k) (c := c) hAne
  have hmn := alignedSet_card_add_min_le (k := k) (c := c) hAne
  have hdd := Str.d0_add
  have hpk := Str.hp
  have hqk := Str.hq
  have hd0p : Str.p - k ≤ Str.d0 := by simp only [Stretch.d0]; omega
  have hd0q : 2 * k + 5 - Str.q ≤ Str.d0 := by simp only [Stretch.d0]; omega
  -- the run visit lies outside the stretch (maximality of the stretch)
  have houts : tau < Str.p ∨ Str.q < tau := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨hcp, hcq⟩ := hcon
    have hxp : c Str.p = c tau := by
      have h := period_iter Str.hper (tau - Str.p) Str.p le_rfl (by rw [hell]; omega)
      rwa [hell, Nat.mul_one, show Str.p + (tau - Str.p) = tau by omega] at h
    have hj2 := hmax j (by omega) ⟨Str.p, le_rfl, by omega, by rw [hxp, hct, hcj]⟩
    omega
  rcases (by omega : j < k ∨ 2 * k + 6 ≤ j) with hjcase | hjcase
  · -- prefix bridge: the non-run visit lies to the right of the aligned block
    have hjgt : (alignedSet k c).max' hAne < j := by
      rcases Nat.lt_or_ge j ((alignedSet k c).min' hAne) with h | h
      · exact (positions_prefix_bridge (by omega) huaw hi1a.1 hi1a.2 h htau1 htau2
          (by rw [hcj, hct])).elim
      · rcases Nat.lt_or_ge ((alignedSet k c).max' hAne) j with h2 | h2
        · exact h2
        · exfalso
          have heq := (mem_alignedSet.1 (hI j h h2)).2
          have := honly (2 * k + 6 + j) (by omega) (by omega) (by rw [← heq, hcj])
          omega
    have hdvd1 : Str.ell ∣ (tau - j) := by rw [hell]; exact one_dvd _
    rcases houts with h | h
    · exact bridge_short_prefix (by omega) huaw Str hjcase htau1 htau2 (by rw [hcj, hct])
        hdvd1 (by omega)
    · exact bridge_span_prefix (by omega) huaw Str hjcase (by omega) htau2
        (by rw [hcj, hct]) hdvd1 (by omega)
  · -- tail bridge
    have hjeq : 2 * k + 6 + (j - (2 * k + 6)) = j := by omega
    have hnotu : j - (2 * k + 6) < k := by
      by_contra hcon
      exact positions_u_not_bridge (by omega) huaw hi1a.1 hi1a.2 htau1 htau2
        (show j = 3 * k + 6 ∨ j = 3 * k + 7 by omega) (by rw [hct, hcj])
    have hjlt : j - (2 * k + 6) < (alignedSet k c).min' hAne := by
      rcases Nat.lt_or_ge ((alignedSet k c).max' hAne) (j - (2 * k + 6)) with h | h
      · exact (positions_tail_bridge (by omega) huaw hi2a.1 hi2a.2 h hnotu htau1 htau2
          (by rw [hjeq, hct, hcj])).elim
      · rcases Nat.lt_or_ge (j - (2 * k + 6)) ((alignedSet k c).min' hAne) with h2 | h2
        · exact h2
        · exfalso
          have heq := (mem_alignedSet.1 (hI _ h2 h)).2
          have := honly (j - (2 * k + 6)) (by omega) (by omega) (by rw [heq, hjeq, hcj])
          omega
    have hdvd1 : Str.ell ∣ (2 * k + 6 + (j - (2 * k + 6)) - tau) := by
      rw [hell]; exact one_dvd _
    rcases houts with h | h
    · exact bridge_span_tail (by omega) huaw Str (by omega) (by omega)
        (by rw [hjeq, hct, hcj]) hdvd1 (by omega)
    · exact bridge_short_tail (by omega) huaw Str (by omega) htau2
        (by rw [hjeq, hct, hcj]) hdvd1 (by omega)

end

end AneVsAn
