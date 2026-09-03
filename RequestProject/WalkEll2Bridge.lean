import RequestProject.WalkChordPair2
import RequestProject.WalkLooseCount2

/-!
# The bridge shape `ℓ = 2` (Proposition 6.8, `prop:ell2bridge`)

This file formalizes Proposition 6.8 (`prop:ell2bridge`) of `anevsanseparationv4.tex`:
in the *bridge shape* `ℓ = 2`, `d₀ = 3`, `r_off = 1`, `(x₁,b₁,s₀) = (1,1,1)` the walk `W`
is not uniquely accepting.

The argument of the source runs as follows.

* By Lemma 6.6(e) (`lem:parity2`, here `no_narrow_of_bridge`) there is no narrow chord,
  so every loose visit belongs to a `γ`-, `δ`- or `PU`-chord, or is the non-run visit of
  the bridge `y`, or is the visit of the singleton.
* *Step 1 (bookkeeping).*  Exactly one of `u₁, u₂` lies in a `PU`-chord and the other one
  is the singleton (`pu_card_and_singleton`); the four tallies of
  `RequestProject/WalkLooseCount2.lean` then read
  `β = 1 + γ`, `r = δ + [pb]`, `β = δ + [tb]`, `r = γ`, whence `[tb] - [pb] = 1`: the
  bridge is a *tail* bridge, `δ = γ = r` and `β = r + 1`.  Since there is at most one
  `γ`-chord (Lemma 5.12(a), `lem:counts`), `r ≤ 1`.
* *Step 2 (`r = 1`).*  Then `J_L = {0,1}`, `J_R = {k-1}`, and the `γ`-chord and the
  `PU`-chord occupy the two prefix indices `0` and `1`.  One order is excluded by the
  Crossing Lemma 4.7 (`lem:cross`), the other gives a `γ`-chord of even shift `k-2`,
  excluded by Corollary 5.8 (`cor:foldloop`).
* *Step 3 (`r = 0`).*  Then `J_L = {0}`, the tail bridge is `h₀ = c_{2k+6}`, and its chord
  `(τ, 2k+6)` has odd length `L` (Lemma 5.13, `lem:bridgeparity`).  The run visits outside
  the stretch force `L = 1` or `L = k+5`; the two cases are killed by the surgeries
  `bridge_loop_triple` and `bridge_insert_triple` below, which traverse the bridge chord
  three times (the "double insertion of the bridge chord" of the source).
-/

namespace AneVsAn

set_option autoImplicit false

section

variable {k : ℕ} {S : Type} {c : ℕ → S}

/-- **Proposition 6.8 (`prop:ell2bridge`), Step 3, the case `L = 1`.**  If the bridge
chord has length `1`, i.e. `c_{2k+5} = c_{2k+6}`, then the `c`-edge is a loop at `h₀` and
the path `W[0,k] R⟨m-2⟩ e_{2k+5} e_{2k+5} e_{2k+5} W[2k+6,n]` is a second accepting path
of length `n`: it uses the run length `m-2 = k+3 ∈ T` and reads `c` at a position where
`W` reads `b`. -/
theorem bridge_loop_triple (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) (hell : Str.ell = 2) (hd : Str.d0 = 3) (hkeven : k % 2 = 0)
    (hloop : c (2 * k + 5) = c (2 * k + 6)) : False := by
  have e1 : Seg k c (c (2 * k + 5)) (c (2 * k + 6)) 1 (fun t => 2 * k + 5 + t) := by
    have h := segW (k := k) c (show 2 * k + 5 ≤ 2 * k + 6 by omega) (by omega)
    rw [show 2 * k + 6 - (2 * k + 5) = 1 by omega] at h
    exact h
  have tl : Seg k c (c (2 * k + 6)) (c (3 * k + 7)) (k + 1) (fun t => 2 * k + 6 + t) := by
    have h := segW (k := k) c (show 2 * k + 6 ≤ 3 * k + 7 by omega) (by omega)
    rw [show 3 * k + 7 - (2 * k + 6) = k + 1 by omega] at h
    exact h
  rw [← hloop] at e1 tl
  refine c_edge_moves hk huaw Str (k / 2) _ (seg_cat e1 (seg_cat e1 (seg_cat e1 tl)))
    (by omega) ?_ ?_ ?_
  · rw [cat_lt (show (0 : ℕ) < 1 by omega)]
  · rw [hd, hell]; omega
  · rw [hd, hell]; omega

/-- **Proposition 6.8 (`prop:ell2bridge`), Step 3, the case `L = k+5`.**  Here the bridge
chord is `(k+1, 2k+6)`, so `α = 2`, `S = [k+2,2k+5]`, and the path
`W[0,k+1] R⟨t₁⟩ e_{2k+5} R⟨t₂⟩ e_{2k+5} R⟨t₃⟩ e_{2k+5} W[2k+6,n]` returns to
`h₀ = c_{k+1}` after each `c`-edge.  With `t₁ = t₂ = 2` and `t₃ = k-2` its length is `n`,
and it has three `c`-edges, the first one at a position where `W` reads `b`. -/
theorem bridge_insert_triple (hk : 18 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) (hell : Str.ell = 2) (hp : Str.p = k + 2) (hq : Str.q = 2 * k + 5)
    (hroff : Str.roff = 1) (hkeven : k % 2 = 0) (hchord : c (k + 1) = c (2 * k + 6)) :
    False := by
  have hslen : ∀ u, Str.slen (k + 1) (2 * k + 5) u = 2 * u + 2 := by
    intro u
    simp only [Stretch.slen, hp, hq, hroff, hell]
    omega
  obtain ⟨τA, hA⟩ := Str.spanSeg (x := k + 1) (y := 2 * k + 5) (by omega) (by omega)
    (by omega) ((k - 4) / 2)
  obtain ⟨τB, hB⟩ := Str.spanSeg (x := k + 1) (y := 2 * k + 5) (by omega) (by omega)
    (by omega) 0
  rw [hslen] at hA hB
  have s0 : Seg k c (c 0) (c (k + 1)) (k + 1) (fun t => 0 + t) := by
    have h := segW (k := k) c (show (0 : ℕ) ≤ k + 1 by omega) (by omega)
    simpa using h
  have E' : Seg k c (c (2 * k + 5)) (c (2 * k + 6)) 1 (fun t => 2 * k + 5 + t) := by
    have h := segW (k := k) c (show 2 * k + 5 ≤ 2 * k + 6 by omega) (by omega)
    rw [show 2 * k + 6 - (2 * k + 5) = 1 by omega] at h
    exact h
  have E : Seg k c (c (2 * k + 5)) (c (k + 1)) 1 (fun t => 2 * k + 5 + t) := by
    rw [hchord]; exact E'
  have tl : Seg k c (c (2 * k + 6)) (c (3 * k + 7)) (k + 1) (fun t => 2 * k + 6 + t) := by
    have h := segW (k := k) c (show 2 * k + 6 ≤ 3 * k + 7 by omega) (by omega)
    rw [show 3 * k + 7 - (2 * k + 6) = k + 1 by omega] at h
    exact h
  have hall := seg_cat s0 (seg_cat hB (seg_cat E (seg_cat hB (seg_cat E
    (seg_cat hA (seg_cat E' tl))))))
  rw [show k + 1 + (2 * 0 + 2 + (1 + (2 * 0 + 2 + (1 + (2 * ((k - 4) / 2) + 2 +
    (1 + (k + 1))))))) = 3 * k + 7 by omega] at hall
  refine no_second_path (by omega : (3 : ℕ) ≤ k) huaw hall (j := k + 3) (by omega) ?_
  have hval : cat (k + 1) (fun t => 0 + t)
      (cat (2 * 0 + 2) τB (cat 1 (fun t => 2 * k + 5 + t)
        (cat (2 * 0 + 2) τB (cat 1 (fun t => 2 * k + 5 + t)
          (cat (2 * ((k - 4) / 2) + 2) τA
            (cat 1 (fun t => 2 * k + 5 + t) (fun t => 2 * k + 6 + t))))))) (k + 3)
      = 2 * k + 5 := by
    rw [cat_ge (by omega), show k + 3 - (k + 1) = 2 by omega, cat_ge (by omega),
      show 2 - (2 * 0 + 2) = 0 by omega, cat_lt (show (0 : ℕ) < 1 by omega)]
  rw [hval, zw_c rfl, zw_b (by omega) (by omega)]
  simp

end

section

variable {k : ℕ} {S : Type} [DecidableEq S] {c : ℕ → S}

/-- **Lemma 5.10(e) (`lem:positions`) and Step 1 of Lemma 5.3 (`lem:gamma`)**, packaged:
the two visits of a bridge `y`.  Its run visit `τ` lies outside the stretch (by the
maximality of the stretch), and its non-run visit is either a prefix time to the right of
the aligned block (a *prefix bridge*) or a tail time `2k+6+j'` with `j'` to the left of
the aligned block (a *tail bridge*); it is not one of the times `3k+6, 3k+7` of
`u₁, u₂`. -/
theorem bridge_visit_data (hk : 18 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c)
    (hmax : ∀ u, u ≤ 3 * k + 7 →
      (∃ x, Str.p ≤ x ∧ x < Str.p + Str.ell ∧ c x = c u) → Str.p ≤ u ∧ u ≤ Str.q)
    {y : S} (hyo : y ∈ onceSet k c) (hyr : (rvis k c y).card = 1)
    {i1 i2 : ℕ} (hi1 : i1 ∈ alignedSet k c) (hi2 : i2 ∈ alignedSet k c)
    (hI : ∀ t, i1 ≤ t → t ≤ i2 → t ∈ alignedSet k c) :
    ∃ tau, k ≤ tau ∧ tau ≤ 2 * k + 5 ∧ c tau = y ∧ (tau < Str.p ∨ Str.q < tau) ∧
      c (dblLo k c y) = y ∧
      ((dblLo k c y < k ∧ i2 < dblLo k c y) ∨
        (2 * k + 6 ≤ dblLo k c y ∧ dblLo k c y < 3 * k + 6 ∧
          dblLo k c y - (2 * k + 6) < i1)) := by
  classical
  have hnv := once_nvis_eq hyo
  have hjmem : dblLo k c y ∈ nvis k c y := by
    rw [hnv]; exact Finset.mem_singleton_self _
  obtain ⟨⟨hjn, hjr⟩, hcj⟩ := mem_nvis_iff.1 hjmem
  set j := dblLo k c y with hjdef
  obtain ⟨tau, htset⟩ := Finset.card_eq_one.1 hyr
  have htmem : tau ∈ rvis k c y := by rw [htset]; exact Finset.mem_singleton_self tau
  simp only [rvis, Finset.mem_filter, runTimes, Finset.mem_Icc] at htmem
  obtain ⟨⟨htau1, htau2⟩, hct⟩ := htmem
  have honly : ∀ t, t < 3 * k + 8 → ¬ (k ≤ t ∧ t ≤ 2 * k + 5) → c t = y → t = j := by
    intro t h1 h2 h3
    have ht : t ∈ nvis k c y := mem_nvis_iff.2 ⟨⟨h1, h2⟩, h3⟩
    rw [hnv, Finset.mem_singleton] at ht
    exact ht
  obtain ⟨hi1k, hi1al⟩ := mem_alignedSet.1 hi1
  obtain ⟨hi2k, hi2al⟩ := mem_alignedSet.1 hi2
  have hchord : c j = c tau := by rw [hcj, hct]
  have hpk := Str.hp
  have hqk := Str.hq
  -- the run visit lies outside the stretch (maximality of the stretch)
  have houts : tau < Str.p ∨ Str.q < tau := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨hcp, hcq⟩ := hcon
    obtain ⟨x, hx1, hx2, hx3⟩ := stretch_state Str hcp hcq
    have hj2 := hmax j (by omega) ⟨x, hx1, hx2, by rw [hx3, hct, hcj]⟩
    omega
  refine ⟨tau, htau1, htau2, hct, houts, hcj, ?_⟩
  rcases (by omega : j < k ∨ 2 * k + 6 ≤ j) with hjcase | hjcase
  · -- prefix bridge
    refine Or.inl ⟨hjcase, ?_⟩
    rcases Nat.lt_or_ge j i1 with h | h
    · exact (positions_prefix_bridge (by omega) huaw hi1k hi1al h htau1 htau2 hchord).elim
    · rcases Nat.lt_or_ge i2 j with h2 | h2
      · exact h2
      · exfalso
        have heq := (mem_alignedSet.1 (hI j h h2)).2
        have := honly (2 * k + 6 + j) (by omega) (by omega) (by rw [← heq, hcj])
        omega
  · -- tail bridge
    have hnotu : j < 3 * k + 6 := by
      by_contra hcon
      exact positions_u_not_bridge (by omega) huaw hi1k hi1al htau1 htau2
        (show j = 3 * k + 6 ∨ j = 3 * k + 7 by omega) hchord.symm
    have hjeq : 2 * k + 6 + (j - (2 * k + 6)) = j := by omega
    refine Or.inr ⟨hjcase, hnotu, ?_⟩
    rcases Nat.lt_or_ge i2 (j - (2 * k + 6)) with h | h
    · exact (positions_tail_bridge (by omega) huaw hi2k hi2al h (by omega) htau1 htau2
        (by rw [hjeq]; exact hchord.symm)).elim
    · rcases Nat.lt_or_ge (j - (2 * k + 6)) i1 with h2 | h2
      · exact h2
      · exfalso
        have heq := (mem_alignedSet.1 (hI _ h2 h)).2
        have := honly (j - (2 * k + 6)) (by omega) (by omega) (by rw [heq, hjeq, hcj])
        omega

/-- **Step 1 of Proposition 6.8 (`prop:ell2bridge`)**, the `u`-states.  In the bridge
shape there is no narrow chord, so neither `u₁` nor `u₂` can be the partner of a tail
state, and neither of them is a bridge (Lemma 5.10(e), `lem:positions`).  Hence each of
them is either the endpoint of a `PU`-chord or the singleton; they cannot both be
`PU`-chords (Lemma 6.6(c), `lem:parity2`, i.e. `no_two_pu`) and they cannot both be
singletons (`s₀ = 1`).  Therefore there is exactly one `PU`-chord and the singleton's
visit is at `3k+6` or `3k+7`, i.e. at neither a prefix nor a tail time. -/
theorem pu_card_and_singleton (hk : 18 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) (hell : Str.ell = 2) (htl : k + 1 ≤ Str.tt * Str.ell)
    (hnarrow : narrowDbl k c = ∅) (hs0 : singleCount k c = 1)
    {i1 : ℕ} (hi1 : i1 ∈ alignedSet k c) :
    (puDbl k c).card = 1 ∧ ∀ z ∈ onceSet k c, (rvis k c z).card = 0 →
      (dblLo k c z = 3 * k + 6 ∨ dblLo k c z = 3 * k + 7) := by
  classical
  have hk3 : (3 : ℕ) ≤ k := by omega
  obtain ⟨hi1k, hi1al⟩ := mem_alignedSet.1 hi1
  have hne12 : c (3 * k + 6) ≠ c (3 * k + 7) := fun h => positions_u1_ne_u2 hk3 huaw Str h
  have hnvu : ∀ v : ℕ, (v = 3 * k + 6 ∨ v = 3 * k + 7) → v ∈ nvis k c (c v) := by
    intro v hv; exact mem_nvis_iff.2 ⟨⟨by omega, by omega⟩, rfl⟩
  have hstu : ∀ v : ℕ, (v = 3 * k + 6 ∨ v = 3 * k + 7) → c v ∈ states k c := by
    intro v hv
    exact mem_states (k := k) (c := c) (t := v) (by simp only [times, Finset.mem_range]; omega)
  have hcase : ∀ v : ℕ, (v = 3 * k + 6 ∨ v = 3 * k + 7) →
      c v ∈ onceSet k c ∨ c v ∈ twiceSet k c := by
    intro v hv
    have h1 : 0 < (nvis k c (c v)).card := Finset.card_pos.2 ⟨v, hnvu v hv⟩
    have h2 := nvis_card_le_two hk3 huaw (c v)
    rcases (by omega : (nvis k c (c v)).card = 1 ∨ (nvis k c (c v)).card = 2) with h | h
    · exact Or.inl (Finset.mem_filter.2 ⟨hstu v hv, h⟩)
    · exact Or.inr (Finset.mem_filter.2 ⟨hstu v hv, h⟩)
  -- a `u`-state with a single visit is the singleton, and its visit is that `u`-time
  have honce : ∀ v : ℕ, (v = 3 * k + 6 ∨ v = 3 * k + 7) → c v ∈ onceSet k c →
      (rvis k c (c v)).card = 0 ∧ dblLo k c (c v) = v := by
    intro v hv hmem
    have hr := rvis_le_one_of_once hk3 huaw hmem
    have hr0 : (rvis k c (c v)).card = 0 := by
      rcases (by omega : (rvis k c (c v)).card = 0 ∨ (rvis k c (c v)).card = 1) with h | h
      · exact h
      · exfalso
        obtain ⟨tau, htset⟩ := Finset.card_eq_one.1 h
        have htmem : tau ∈ rvis k c (c v) := by
          rw [htset]; exact Finset.mem_singleton_self _
        simp only [rvis, Finset.mem_filter, runTimes, Finset.mem_Icc] at htmem
        exact positions_u_not_bridge hk3 huaw hi1k hi1al htmem.1.1 htmem.1.2 hv htmem.2
    refine ⟨hr0, ?_⟩
    have hnv := once_nvis_eq hmem
    have hvm := hnvu v hv
    rw [hnv, Finset.mem_singleton] at hvm
    exact hvm.symm
  -- a `u`-state with two visits is a `PU`-double
  have htwice : ∀ v : ℕ, (v = 3 * k + 6 ∨ v = 3 * k + 7) → c v ∈ twiceSet k c →
      c v ∈ puDbl k c ∧ dblLo k c (c v) < k ∧ dblHi k c (c v) = v ∧
        c (dblLo k c (c v)) = c v := by
    intro v hv hmem
    have hw : c v ∈ wideDbl k c := by
      rcases Finset.mem_union.1 (twiceSet_subset_union hmem) with h | h
      · rw [hnarrow] at h; exact absurd h (Finset.notMem_empty _)
      · exact h
    obtain ⟨hlok, hhige, hhin, hclo, hchi⟩ := wideDbl_facts hw
    have hvle : v ≤ dblHi k c (c v) := le_dblHi (hnvu v hv)
    have hhiv : dblHi k c (c v) = v := by
      rcases hv with h | h
      · rcases (by omega : dblHi k c (c v) = 3 * k + 6 ∨ dblHi k c (c v) = 3 * k + 7)
          with h' | h'
        · omega
        · exact absurd (by rw [← h', hchi, h]) hne12
      · omega
    exact ⟨Finset.mem_filter.2 ⟨hw, by omega⟩, hlok, hhiv, hclo⟩
  -- the two `u`-states are not both doubles
  have hnotboth : ¬ (c (3 * k + 6) ∈ twiceSet k c ∧ c (3 * k + 7) ∈ twiceSet k c) := by
    rintro ⟨h1, h2⟩
    obtain ⟨-, hlo1, hhi1, hclo1⟩ := htwice _ (Or.inl rfl) h1
    obtain ⟨-, hlo2, hhi2, hclo2⟩ := htwice _ (Or.inr rfl) h2
    refine no_two_pu hk3 huaw Str hell htl hi1k hi1al hlo1 hlo2 ?_ hclo1 hclo2
    intro h
    exact hne12 (by rw [← hclo1, h, hclo2])
  -- the two `u`-states are not both singletons
  have hnotboth' : ¬ (c (3 * k + 6) ∈ onceSet k c ∧ c (3 * k + 7) ∈ onceSet k c) := by
    rintro ⟨h1, h2⟩
    obtain ⟨hr1, -⟩ := honce _ (Or.inl rfl) h1
    obtain ⟨hr2, -⟩ := honce _ (Or.inr rfl) h2
    have hsub : ({c (3 * k + 6), c (3 * k + 7)} : Finset S) ⊆
        (onceSet k c).filter (fun s => (rvis k c s).card = 0) := by
      intro s hs
      rcases Finset.mem_insert.1 hs with h | h
      · rw [h]; exact Finset.mem_filter.2 ⟨h1, hr1⟩
      · rw [Finset.mem_singleton.1 h]; exact Finset.mem_filter.2 ⟨h2, hr2⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_pair hne12] at hcard
    rw [singleCount] at hs0
    omega
  -- so exactly one of them is a double, and it is the unique `PU`-chord
  have key : ∀ v w : ℕ, (v = 3 * k + 6 ∨ v = 3 * k + 7) → (w = 3 * k + 6 ∨ w = 3 * k + 7) →
      c v ∈ twiceSet k c → c w ∈ onceSet k c →
      ((puDbl k c).card = 1 ∧ ∀ z ∈ onceSet k c, (rvis k c z).card = 0 →
        (dblLo k c z = 3 * k + 6 ∨ dblLo k c z = 3 * k + 7)) := by
    intro v w hv hw hvd hwo
    obtain ⟨hpuv, -, hhiv, -⟩ := htwice v hv hvd
    obtain ⟨hrw0, hlow⟩ := honce w hw hwo
    have hwnotd : c w ∉ twiceSet k c := by
      intro hcon
      simp only [onceSet, twiceSet, Finset.mem_filter] at hwo hcon
      omega
    have hvwne : v ≠ w := by
      rintro rfl
      exact hwnotd hvd
    have hvals : (v = 3 * k + 6 ∧ w = 3 * k + 7) ∨ (v = 3 * k + 7 ∧ w = 3 * k + 6) := by
      omega
    have hsing : (onceSet k c).filter (fun s => (rvis k c s).card = 0) = {c w} := by
      have hmem : c w ∈ (onceSet k c).filter (fun s => (rvis k c s).card = 0) :=
        Finset.mem_filter.2 ⟨hwo, hrw0⟩
      obtain ⟨a, ha⟩ := Finset.card_eq_one.1 (show ((onceSet k c).filter
        (fun s => (rvis k c s).card = 0)).card = 1 from hs0)
      rw [ha] at hmem ⊢
      rw [Finset.mem_singleton.1 hmem]
    refine ⟨?_, ?_⟩
    · -- `puDbl` is exactly `{c v}`
      refine Finset.card_eq_one.2 ⟨c v, Finset.eq_singleton_iff_unique_mem.2 ⟨hpuv, ?_⟩⟩
      intro s hs
      obtain ⟨hw2, hhis⟩ := Finset.mem_filter.1 hs
      obtain ⟨-, -, hhin, -, hchi⟩ := wideDbl_facts hw2
      have hstw : s ∈ twiceSet k c := (Finset.mem_filter.1 hw2).1
      have hs2 : s = c v ∨ s = c w := by
        rcases (by omega : dblHi k c s = 3 * k + 6 ∨ dblHi k c s = 3 * k + 7) with h | h
        · rcases hvals with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl (by rw [← hchi, h, h1])
          · exact Or.inr (by rw [← hchi, h, h2])
        · rcases hvals with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inr (by rw [← hchi, h, h2])
          · exact Or.inl (by rw [← hchi, h, h1])
      rcases hs2 with h | h
      · exact h
      · exact absurd (h ▸ hstw) hwnotd
    · intro z hz hrz
      have hzm : z ∈ (onceSet k c).filter (fun s => (rvis k c s).card = 0) :=
        Finset.mem_filter.2 ⟨hz, hrz⟩
      rw [hsing, Finset.mem_singleton] at hzm
      rw [hzm, hlow]
      exact hw
  rcases hcase (3 * k + 6) (Or.inl rfl) with h1 | h1
  · rcases hcase (3 * k + 7) (Or.inr rfl) with h2 | h2
    · exact absurd ⟨h1, h2⟩ hnotboth'
    · exact key (3 * k + 7) (3 * k + 6) (Or.inr rfl) (Or.inl rfl) h2 h1
  · rcases hcase (3 * k + 7) (Or.inr rfl) with h2 | h2
    · exact key (3 * k + 6) (3 * k + 7) (Or.inl rfl) (Or.inr rfl) h1 h2
    · exact absurd ⟨h1, h2⟩ hnotboth

/-- **Proposition 6.8 (`prop:ell2bridge`)**: the bridge shape `ℓ = 2`, `d₀ = 3`,
`r_off = 1`, `(x₁,b₁,s₀) = (1,1,1)` is impossible.  See the module docstring for the
three steps of the argument of the source. -/
theorem ell2_bridge (hk : 18 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) (hell : Str.ell = 2) (hd : Str.d0 = 3) (hroff : Str.roff = 1)
    (hb : bridgeCount k c = 1) (hs0 : singleCount k c = 1)
    (hmax : ∀ u, u ≤ 3 * k + 7 →
      (∃ x, Str.p ≤ x ∧ x < Str.p + Str.ell ∧ c x = c u) → Str.p ≤ u ∧ u ≤ Str.q)
    {i0 : ℕ} (hi0 : i0 < k) (halign0 : c i0 = c (2 * k + 6 + i0)) : False := by
  classical
  have hk3 : (3 : ℕ) ≤ k := by omega
  have hadd := Str.d0_add
  rw [hd, hell] at hadd
  have hkeven : k % 2 = 0 := by omega
  have htl : Str.tt * Str.ell = k + 2 := by rw [hell]; omega
  have hpk := Str.hp
  have hqk := Str.hq
  have hdd : (Str.p - k) + (2 * k + 5 - Str.q) = 2 := by
    have h := hd
    simp only [Stretch.d0, hroff] at h
    omega
  -- the aligned block `[i1,i2]`
  have hAne : (alignedSet k c).Nonempty := ⟨i0, mem_alignedSet.2 ⟨hi0, halign0⟩⟩
  obtain ⟨i1, i2, hi1, hi2, hlb, hub, hI⟩ :
      ∃ i1 i2, i1 ∈ alignedSet k c ∧ i2 ∈ alignedSet k c ∧
        (∀ t ∈ alignedSet k c, i1 ≤ t) ∧ (∀ t ∈ alignedSet k c, t ≤ i2) ∧
        (∀ t, i1 ≤ t → t ≤ i2 → t ∈ alignedSet k c) :=
    ⟨_, _, Finset.min'_mem _ hAne, Finset.max'_mem _ hAne,
      fun t ht => Finset.min'_le _ _ ht, fun t ht => Finset.le_max' _ _ ht,
      alignedSet_interval hk3 huaw hAne⟩
  have hi1k := (mem_alignedSet.1 hi1).1
  have hi2k := (mem_alignedSet.1 hi2).1
  have hi1al := (mem_alignedSet.1 hi1).2
  have hi2al := (mem_alignedSet.1 hi2).2
  have hi12 : i1 ≤ i2 := hlb _ hi2
  -- there is no narrow chord (Lemma 6.6(e), `lem:parity2`)
  have hnarrow : narrowDbl k c = ∅ :=
    no_narrow_of_bridge hk huaw Str hell (by omega) (by rw [hell, hb, hs0]; omega) hmax (by omega)
  -- Step 1: exactly one `PU`-chord, and the singleton is visited at `3k+6` or `3k+7`
  obtain ⟨hpu1, hsingle⟩ :=
    pu_card_and_singleton hk huaw Str hell (by omega) hnarrow hs0 hi1
  -- the bridge `y`
  rw [bridgeCount] at hb
  obtain ⟨y, hyset⟩ := Finset.card_eq_one.1 hb
  have hymem : y ∈ (onceSet k c).filter (fun s => (rvis k c s).card = 1) := by
    rw [hyset]; exact Finset.mem_singleton_self y
  obtain ⟨hyo, hyr⟩ := Finset.mem_filter.1 hymem
  obtain ⟨tau, htau1, htau2, hctau, houts, hcy, hpos⟩ :=
    bridge_visit_data hk huaw Str hmax hyo hyr hi1 hi2 hI
  -- the loose visits in a block of non-run times: only the bridge can contribute
  have honceIn : ∀ A : Finset ℕ, (∀ t ∈ A, t < 3 * k + 6) →
      (onceIn k c A).card = if dblLo k c y ∈ A then 1 else 0 := by
    intro A hA
    have hsub : onceIn k c A ⊆ {y} := by
      intro z hz
      rw [onceIn, Finset.mem_filter] at hz
      obtain ⟨hzo, hzA⟩ := hz
      have hr := rvis_le_one_of_once hk3 huaw hzo
      rcases (by omega : (rvis k c z).card = 0 ∨ (rvis k c z).card = 1) with h | h
      · exact absurd (hA _ hzA) (by
          have := hsingle z hzo h
          omega)
      · have hzm : z ∈ (onceSet k c).filter (fun s => (rvis k c s).card = 1) :=
          Finset.mem_filter.2 ⟨hzo, h⟩
        rw [hyset] at hzm
        exact hzm
    by_cases hmem : dblLo k c y ∈ A
    · rw [if_pos hmem]
      have he : onceIn k c A = {y} :=
        Finset.Subset.antisymm hsub (by
          intro z hz
          rw [Finset.mem_singleton] at hz
          subst hz
          exact Finset.mem_filter.2 ⟨hyo, hmem⟩)
      rw [he, Finset.card_singleton]
    · rw [if_neg hmem]
      have he : onceIn k c A = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro z hz
        have hzy := Finset.mem_singleton.1 (hsub hz)
        subst hzy
        exact hmem (Finset.mem_filter.1 hz).2
      rw [he, Finset.card_empty]
  -- the four tallies of Step 1
  have hT1 := count_prefix_left_gen hk3 huaw hi1 hi2 hlb hI
  have hT2 := count_prefix_right_gen hk3 huaw hi1 hi2 hlb hub hI
  have hT3 := count_tail_left_gen hk3 huaw hi1 hi2 hlb hI
  have hT4 := count_tail_right_gen hk3 huaw hi1 hi2 hlb hub hI
  rw [hnarrow] at hT1 hT2 hT3 hT4
  simp only [Finset.filter_empty, Finset.card_empty, Nat.zero_add,
    Nat.add_zero] at hT1 hT2 hT3 hT4
  rw [hpu1] at hT1
  rw [honceIn _ (by intro t ht; rw [Finset.mem_range] at ht; omega)] at hT1
  rw [honceIn _ (by intro t ht; rw [Finset.mem_Ico] at ht; omega)] at hT2
  rw [honceIn _ (by intro t ht; rw [Finset.mem_Ico] at ht; omega)] at hT3
  rw [honceIn _ (by intro t ht; rw [Finset.mem_Ico] at ht; omega)] at hT4
  simp only [Finset.mem_range, Finset.mem_Ico] at hT1 hT2 hT3 hT4
  have hgle := gammaDbl_card_le hk huaw Str (by omega) hi1 hi2 hlb
  rw [hell] at hgle
  -- the bridge is a tail bridge, and `r = γ = δ ≤ 1`
  have hcases : (2 * k + 6 ≤ dblLo k c y ∧ dblLo k c y < 3 * k + 6 ∧
        dblLo k c y - (2 * k + 6) < i1) ∧
      (((gammaDbl k c i1).card = 0 ∧ i1 = 1 ∧ i2 = k - 1) ∨
        ((gammaDbl k c i1).card = 1 ∧ i1 = 2 ∧ i2 = k - 2)) := by
    rcases hpos with hp | hp
    · exact absurd hp (by split_ifs at hT1 hT2 hT3 hT4 <;> omega)
    · exact ⟨hp, by split_ifs at hT1 hT2 hT3 hT4 <;> omega⟩
  obtain ⟨⟨hylo1, hylo2, hylo3⟩, hcases⟩ := hcases
  rcases hcases with ⟨hg0, hi1v, hi2v⟩ | ⟨hg1, hi1v, hi2v⟩
  · -- **Step 3**: `r = 0`, so `J_L = {0}` and the tail bridge is `h₀ = c_{2k+6}`
    have hjy : dblLo k c y = 2 * k + 6 := by omega
    have hchord : c tau = c (2 * k + 6) := by rw [hctau, ← hjy, hcy]
    -- the bridge chord has odd length (Lemma 5.13, `lem:bridgeparity`)
    have hodd : (2 * k + 6 - tau) % 2 = 1 := by
      by_contra hcon
      have hdvd : Str.ell ∣ (2 * k + 6 + 0 - tau) := by
        rw [hell]; omega
      rcases houts with hlt | hgt
      · exact bridge_span_tail hk3 huaw Str (jp := 0) (tau := tau) (by omega) (by omega)
          (by simpa using hchord) hdvd (by omega)
      · exact bridge_short_tail hk3 huaw Str (jp := 0) (tau := tau) (by omega) (by omega)
          (by simpa using hchord) hdvd (by omega)
    rcases houts with hlt | hgt
    · -- `τ = k+1`, so `α = 2` and the stretch is `[k+2, 2k+5]`
      have htv : tau = k + 1 := by omega
      exact bridge_insert_triple hk huaw Str hell (by omega) (by omega) hroff hkeven
        (by rw [← htv]; exact hchord)
    · -- `τ = 2k+5`: the `c`-edge is a loop
      have htv : tau = 2 * k + 5 := by omega
      exact bridge_loop_triple hk3 huaw Str hell hd hkeven (by rw [← htv]; exact hchord)
  · -- **Step 2**: `r = 1`, so `J_L = {0,1}` and the `γ`- and `PU`-chords sit there
    obtain ⟨sg, hsgset⟩ := Finset.card_eq_one.1 hg1
    have hsg : sg ∈ gammaDbl k c i1 := by rw [hsgset]; exact Finset.mem_singleton_self sg
    obtain ⟨spu, hspuset⟩ := Finset.card_eq_one.1 hpu1
    have hspu : spu ∈ puDbl k c := by rw [hspuset]; exact Finset.mem_singleton_self spu
    obtain ⟨hglo1, hglok, hghige, hghile, hghi2⟩ := gammaDbl_pos hk3 huaw hi1 hI hsg
    obtain ⟨hplo1, hphige, hphile⟩ := puDbl_pos hk3 huaw hi1 hspu
    obtain ⟨-, -, -, hgclo, hgchi⟩ := wideDbl_facts (Finset.mem_filter.1 hsg).1
    obtain ⟨-, -, -, hpclo, hpchi⟩ := wideDbl_facts (puDbl_subset_wide hspu)
    have hghiv : dblHi k c sg = 3 * k + 5 := by omega
    have hne : dblLo k c sg ≠ dblLo k c spu := by
      intro h
      refine Finset.disjoint_left.1 (disj_gamma_pu (k := k) (c := c) (i1 := i1)) hsg ?_
      rw [show sg = spu by rw [← hgclo, h, hpclo]]
      exact hspu
    rcases lt_or_gt_of_ne hne with h | h
    · -- the `γ`-chord starts at `0` and the `PU`-chord at `1`: the Crossing Lemma 4.7
      have hgz : dblLo k c sg = 0 := by omega
      obtain ⟨hcr, -⟩ := crossing hk3 huaw (a₁ := dblLo k c sg) (b₁ := dblLo k c spu)
        (a₂ := 3 * k + 5) (b₂ := dblHi k c spu) h (by omega) (by omega) (by omega)
        (by rw [hgclo, ← hghiv, hgchi]) (hpclo.trans hpchi.symm)
      rw [zw_d (by omega) rfl, hgz, zw_a (by omega)] at hcr
      simp at hcr
    · -- the `γ`-chord starts at `1`: an even shift `k-2`, excluded by Corollary 5.8
      have hgo : dblLo k c sg = 1 := by omega
      refine foldloop_lt hk3 huaw Str (i := i1) (j := dblLo k c sg) (j' := k - 1)
        (by omega) (by omega) (by omega) (by omega) hi1al ?_ ?_ ?_
      · rw [hgclo, show 2 * k + 6 + (k - 1) = 3 * k + 5 by omega, ← hghiv, hgchi]
      · rw [hell]; omega
      · omega

end

end AneVsAn
