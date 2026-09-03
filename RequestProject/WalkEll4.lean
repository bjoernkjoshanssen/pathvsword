import RequestProject.WalkEll2

/-!
# The shape `ℓ = 4` (Proposition 6.5, `prop:ell4`)

This file formalizes Proposition 6.5 (`prop:ell4`) of `ane-vs-an-separation-v4_1.tex`:
the shape `ℓ = 4`, `d₀ ∈ {1,3}`, `x₁ = b₁ = s₀ = 0` is impossible.

The two steps of the source are:

* *Step 1* (`narrow_len_seven_or_nine`, `narrow_card_le_one`): every narrow chord has
  length `7` or `9` — its length is nonzero modulo `4` by Lemma 5.6(a) (`lem:narrow`),
  it is not `≡ 2 (mod 4)` by Lemma 5.6(b) with `σ = 2`, and it is not an odd number `≤ 5`
  by Lemma 5.6(b) with `σ = 4` — and there is at most one of them, because two of them
  would have either equal residues modulo `4` (excluded by Lemma 5.6(c),
  `narrow_pair_mod`) or lengths `7` and `9`, whose sum `16` is a multiple of `4` at most
  `tℓ` (excluded by Lemma 5.6(d), `narrow_pair_sum`).
* *Step 2* (`ell4`): the loose visits are counted by position.  The four tallies of
  `RequestProject/WalkLooseCount.lean` are the four counts
  `β = 2 PP_L + PU + γ`, `r = 2 PP_R + δ`, `β = 2 TT_L + δ`, `r = 2 TT_R + TU + γ`
  of the source, and `pu_tu_count` is the count `PU + TU = 2` of the two `u`-visits.
  The classification `narrow_type` of the unique narrow chord into the five kinds
  `PP_L, PP_R, TT_L, TT_R, TU` is Lemma 5.10 (`lem:positions`); in each kind either the
  four tallies are already contradictory or they force the side of the chord to be too
  short to accommodate a chord of length `7`.
-/

namespace AneVsAn

set_option autoImplicit false

section

variable {k : ℕ} {S : Type} [DecidableEq S] {c : ℕ → S}

/-- **Lemma 5.6(a) (Narrow surgeries, `lem:narrow`)** in the form used below: a narrow
chord whose length is divisible by `ℓ` can be skipped. -/
theorem narrow_dead_skip (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) {s : S} (hs : s ∈ narrowDbl k c)
    (hdvd : Str.ell ∣ (dblHi k c s - dblLo k c s)) : False := by
  rw [narrowDbl, Finset.mem_filter] at hs
  obtain ⟨hlt, -, -, hhin, hclo, hchi⟩ := dbl_chord hs.1
  have heq : c (dblLo k c s) = c (dblHi k c s) := by rw [hclo, hchi]
  rcases hs.2 with h | h
  · exact narrow_prefix_skip hk huaw Str hlt h heq hdvd
  · exact narrow_tail_skip hk huaw Str h hlt hhin heq hdvd

/-- **Lemma 5.6(b) (Narrow surgeries, `lem:narrow`)** in the form used below: a narrow
chord of length `λ` with `ℓ ∣ σλ` and `σλ ≤ tℓ` gives the `σ`-fold insertion. -/
theorem narrow_dead_insert (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) {s : S} (hs : s ∈ narrowDbl k c) {σ : ℕ} (hσ : 1 ≤ σ)
    (hdvd : Str.ell ∣ σ * (dblHi k c s - dblLo k c s))
    (hle : σ * (dblHi k c s - dblLo k c s) ≤ Str.tt * Str.ell) : False := by
  rw [narrowDbl, Finset.mem_filter] at hs
  obtain ⟨hlt, -, -, hhin, hclo, hchi⟩ := dbl_chord hs.1
  have heq : c (dblLo k c s) = c (dblHi k c s) := by rw [hclo, hchi]
  rcases hs.2 with h | h
  · exact narrow_prefix_insert hk huaw Str hlt h heq hσ hdvd hle
  · exact narrow_tail_insert hk huaw Str h hlt hhin heq hσ hdvd hle

/-- **Step 1 of Proposition 6.5 (`prop:ell4`)**: for `ℓ = 4` a narrow chord of length at
most `10` has length `7` or `9`.  A length divisible by `4` is excluded by
Lemma 5.6(a); a length `≡ 2 (mod 4)` by Lemma 5.6(b) with `σ = 2` (then `2λ ≤ 20 ≤ tℓ`);
an odd length `≤ 5` by Lemma 5.6(b) with `σ = 4` (then `4λ ≤ 20 ≤ tℓ`). -/
theorem narrow_len_seven_or_nine (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) (hell : Str.ell = 4) (htl : 20 ≤ Str.tt * Str.ell)
    {s : S} (hs : s ∈ narrowDbl k c) (hle : dblHi k c s - dblLo k c s ≤ 10) :
    dblHi k c s - dblLo k c s = 7 ∨ dblHi k c s - dblLo k c s = 9 := by
  obtain ⟨hlt, -, -, -, -, -⟩ := dbl_chord (Finset.mem_filter.1 hs).1
  by_contra hcon
  push_neg at hcon
  obtain ⟨h7, h9⟩ := hcon
  rcases (by omega : (dblHi k c s - dblLo k c s) % 4 = 0 ∨
      (dblHi k c s - dblLo k c s) % 4 = 2 ∨ (dblHi k c s - dblLo k c s) % 2 = 1)
    with h | h | h
  · exact narrow_dead_skip hk huaw Str hs (by rw [hell]; exact Nat.dvd_of_mod_eq_zero h)
  · refine narrow_dead_insert hk huaw Str hs (σ := 2) (by omega) ?_ (by omega)
    obtain ⟨q, hq⟩ : ∃ q, dblHi k c s - dblLo k c s = 4 * q + 2 :=
      ⟨(dblHi k c s - dblLo k c s) / 4, by omega⟩
    rw [hell]
    exact ⟨2 * q + 1, by omega⟩
  · refine narrow_dead_insert hk huaw Str hs (σ := 4) (by omega) ?_ (by omega)
    exact ⟨dblHi k c s - dblLo k c s, by rw [hell]⟩

/-- **Step 1 of Proposition 6.5 (`prop:ell4`), conclusion**: if `ℓ = 4` and every narrow
chord has length `7` or `9`, then there is at most one narrow chord.  Two of them would
have either equal lengths — hence equal residues modulo `4`, excluded by Lemma 5.6(c)
(`lem:narrow`) — or lengths `7` and `9`, whose sum `16` is a multiple of `4` at most
`tℓ`, excluded by Lemma 5.6(d). -/
theorem narrow_card_le_one (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) (hell : Str.ell = 4) (htl : 20 ≤ Str.tt * Str.ell)
    (htlk : k ≤ Str.tt * Str.ell)
    (hlen : ∀ s ∈ narrowDbl k c, dblHi k c s - dblLo k c s = 7 ∨
      dblHi k c s - dblLo k c s = 9) :
    (narrowDbl k c).card ≤ 1 := by
  classical
  have key : ∀ a ∈ narrowDbl k c, ∀ b ∈ narrowDbl k c,
      dblLo k c a < dblLo k c b → False := by
    intro a ha b hb hlo
    obtain ⟨hlta, -, -, hhina, hcloa, hchia⟩ := dbl_chord (Finset.mem_filter.1 ha).1
    obtain ⟨hltb, -, -, hhinb, hclob, hchib⟩ := dbl_chord (Finset.mem_filter.1 hb).1
    have hna : dblHi k c a < k ∨ (2 * k + 6 ≤ dblLo k c a ∧ dblHi k c a ≤ 3 * k + 7) := by
      rcases (Finset.mem_filter.1 ha).2 with h | h
      exacts [Or.inl h, Or.inr ⟨h, hhina⟩]
    have hnb : dblHi k c b < k ∨ (2 * k + 6 ≤ dblLo k c b ∧ dblHi k c b ≤ 3 * k + 7) := by
      rcases (Finset.mem_filter.1 hb).2 with h | h
      exacts [Or.inl h, Or.inr ⟨h, hhinb⟩]
    have hea : c (dblLo k c a) = c (dblHi k c a) := by rw [hcloa, hchia]
    have heb : c (dblLo k c b) = c (dblHi k c b) := by rw [hclob, hchib]
    have hla := hlen a ha
    have hlb := hlen b hb
    rcases (by omega : dblHi k c a - dblLo k c a = dblHi k c b - dblLo k c b ∨
        (dblHi k c a - dblLo k c a) + (dblHi k c b - dblLo k c b) = 16) with h | h
    · exact narrow_pair_mod hk huaw Str htlk hlta hltb hlo hna hnb hea heb (by rw [h])
    · exact narrow_pair_sum hk huaw Str hlta hltb hlo hna hnb hea heb
        (by rw [hell, h]; exact ⟨4, rfl⟩) (by omega)
  by_contra hcon
  obtain ⟨a, ha, b, hb, hab⟩ :=
    Finset.one_lt_card.1 (show 1 < (narrowDbl k c).card by omega)
  obtain ⟨-, -, -, -, hcloa, -⟩ := dbl_chord (Finset.mem_filter.1 ha).1
  obtain ⟨-, -, -, -, hclob, -⟩ := dbl_chord (Finset.mem_filter.1 hb).1
  have hlone : dblLo k c a ≠ dblLo k c b := fun h => hab (by rw [← hcloa, ← hclob, h])
  rcases lt_or_gt_of_ne hlone with h | h
  · exact key a ha b hb h
  · exact key b hb a ha h

/-- **Lemma 5.10 (Position constraints, `lem:positions`)**, in the form used by Step 2 of
Proposition 6.5 (`prop:ell4`): a narrow chord is of exactly one of the five kinds
`PP_L` (both indices in `J_L`), `PP_R` (both in `J_R`), `TT_L`, `TT_R` and `TU` (a tail
index in `J_R` paired with `u₁` or `u₂`). -/
theorem narrow_type (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c) (Str : Stretch k c)
    {i1 i2 : ℕ} (hi1 : i1 ∈ alignedSet k c) (hi2 : i2 ∈ alignedSet k c) (h12 : i1 ≤ i2)
    (hI : ∀ t, i1 ≤ t → t ≤ i2 → t ∈ alignedSet k c)
    {s : S} (hs : s ∈ narrowDbl k c) :
    dblHi k c s < i1 ∨
      (i2 < dblLo k c s ∧ dblHi k c s < k) ∨
      (2 * k + 6 ≤ dblLo k c s ∧ dblHi k c s < 2 * k + 6 + i1) ∨
      (2 * k + 6 + i2 < dblLo k c s ∧ dblHi k c s < 3 * k + 6) ∨
      (2 * k + 6 + i2 < dblLo k c s ∧ dblLo k c s < 3 * k + 6 ∧
        3 * k + 6 ≤ dblHi k c s) := by
  have hst : s ∈ twiceSet k c := (Finset.mem_filter.1 hs).1
  obtain ⟨hlt, hlos, hhis, hhin, hclo, hchi⟩ := dbl_chord hst
  have hnv := dbl_nvis_nonempty hst
  have hmlo := dblLo_mem hnv
  have hmhi := dblHi_mem hnv
  have hi1k := (mem_alignedSet.1 hi1).1
  have hi2k := (mem_alignedSet.1 hi2).1
  have hi1al := (mem_alignedSet.1 hi1).2
  have hi2al := (mem_alignedSet.1 hi2).2
  rcases (Finset.mem_filter.1 hs).2 with hpre | htail
  · -- a prefix chord `(j₁, j₂)`, `j₁ < j₂ ≤ k-1`
    have hloNA : ¬ (i1 ≤ dblLo k c s ∧ dblLo k c s ≤ i2) := by
      rintro ⟨ha, hb⟩
      have hal := (mem_alignedSet.1 (hI _ ha hb)).2
      have h3 : 2 * k + 6 + dblLo k c s ∈ nvis k c s :=
        mem_nvis_iff.2 ⟨⟨by omega, by omega⟩, by rw [← hal]; exact hclo⟩
      exact no_three_nvis hk huaw hmlo hmhi h3 (by omega) (by omega) (by omega)
    have hhiNA : ¬ (i1 ≤ dblHi k c s ∧ dblHi k c s ≤ i2) := by
      rintro ⟨ha, hb⟩
      have hal := (mem_alignedSet.1 (hI _ ha hb)).2
      have h3 : 2 * k + 6 + dblHi k c s ∈ nvis k c s :=
        mem_nvis_iff.2 ⟨⟨by omega, by omega⟩, by rw [← hal]; exact hchi⟩
      exact no_three_nvis hk huaw hmlo hmhi h3 (by omega) (by omega) (by omega)
    have hstr : ¬ (dblLo k c s < i1 ∧ i1 < dblHi k c s) := by
      rintro ⟨ha, hb⟩
      exact positions_PP hk huaw hi1k hi1al ha hb hpre (by rw [hclo, hchi])
    omega
  · -- a tail chord
    by_cases hu : 3 * k + 6 ≤ dblHi k c s
    · -- a `TU`-chord
      have hlo5 : dblLo k c s < 3 * k + 6 := by
        by_contra hcon
        have hd1 : dblLo k c s = 3 * k + 6 := by omega
        have hd2 : dblHi k c s = 3 * k + 7 := by omega
        exact positions_u1_ne_u2 hk huaw Str (by rw [← hd1, ← hd2, hclo, hchi])
      obtain ⟨j, hj⟩ : ∃ j, dblLo k c s = 2 * k + 6 + j := ⟨dblLo k c s - (2 * k + 6), by omega⟩
      have hjk : j < k := by omega
      have hchord : c (2 * k + 6 + j) = c (dblHi k c s) := by rw [← hj, hclo, hchi]
      have hNA : ¬ (i1 ≤ j ∧ j ≤ i2) := by
        rintro ⟨ha, hb⟩
        have hal := (mem_alignedSet.1 (hI _ ha hb)).2
        have h3 : j ∈ nvis k c s :=
          mem_nvis_iff.2 ⟨⟨by omega, by omega⟩, by rw [hal, ← hj]; exact hclo⟩
        exact no_three_nvis hk huaw h3 hmlo hmhi (by omega) (by omega) (by omega)
      have hgt : i2 < j := by
        rcases (by omega : j < i2 ∨ i2 ≤ j) with h | h
        · exact absurd (positions_TU hk huaw hi2k hi2al h (by omega) hchord) (fun h => h.elim)
        · omega
      omega
    · -- a `TT`-chord
      obtain ⟨j1, hj1⟩ : ∃ j, dblLo k c s = 2 * k + 6 + j :=
        ⟨dblLo k c s - (2 * k + 6), by omega⟩
      obtain ⟨j2, hj2⟩ : ∃ j, dblHi k c s = 2 * k + 6 + j :=
        ⟨dblHi k c s - (2 * k + 6), by omega⟩
      have hj1k : j1 < k := by omega
      have hj2k : j2 < k := by omega
      have hchord : c (2 * k + 6 + j1) = c (2 * k + 6 + j2) := by
        rw [← hj1, ← hj2, hclo, hchi]
      have h1NA : ¬ (i1 ≤ j1 ∧ j1 ≤ i2) := by
        rintro ⟨ha, hb⟩
        have hal := (mem_alignedSet.1 (hI _ ha hb)).2
        have h3 : j1 ∈ nvis k c s :=
          mem_nvis_iff.2 ⟨⟨by omega, by omega⟩, by rw [hal, ← hj1]; exact hclo⟩
        exact no_three_nvis hk huaw h3 hmlo hmhi (by omega) (by omega) (by omega)
      have h2NA : ¬ (i1 ≤ j2 ∧ j2 ≤ i2) := by
        rintro ⟨ha, hb⟩
        have hal := (mem_alignedSet.1 (hI _ ha hb)).2
        have h3 : j2 ∈ nvis k c s :=
          mem_nvis_iff.2 ⟨⟨by omega, by omega⟩, by rw [hal, ← hj2]; exact hchi⟩
        exact no_three_nvis hk huaw h3 hmlo hmhi (by omega) (by omega) (by omega)
      have hstr : ¬ (j1 < i1 ∧ i1 < j2) := by
        rintro ⟨ha, hb⟩
        exact positions_TT hk huaw hi1k hi1al ha hb (by omega) hchord
      omega

/-- **The count of the two `u`-visits, Step 2 of Proposition 6.5 (`prop:ell4`)**:
`PU + TU = 2`.  Each of `u₁ = c_{3k+6}` and `u₂ = c_{3k+7}` is a double whose later
non-run visit is its own, so its chord is either a `PU`-chord (a wide chord ending at a
`u`-state) or a narrow `TU`-chord; conversely each such chord contains one of `u₁, u₂`,
and `u₁ ≠ u₂` by Lemma 5.10(f) (`lem:positions`). -/
theorem pu_tu_count (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c) (Str : Stretch k c)
    (hb : bridgeCount k c = 0) (hs0 : singleCount k c = 0) :
    (puDbl k c).card
      + ((narrowDbl k c).filter (fun s => 3 * k + 6 ≤ dblHi k c s)).card = 2 := by
  classical
  have hs1 : c (3 * k + 6) ∈ twiceSet k c :=
    nonrun_double hk huaw hb hs0 (mem_nonRunTimes_of (by omega) (by omega))
  have hs2 : c (3 * k + 7) ∈ twiceSet k c :=
    nonrun_double hk huaw hb hs0 (mem_nonRunTimes_of (by omega) (by omega))
  have hs1nv : 3 * k + 6 ∈ nvis k c (c (3 * k + 6)) :=
    mem_nvis_iff.2 ⟨⟨by omega, by omega⟩, rfl⟩
  have hs2nv : 3 * k + 7 ∈ nvis k c (c (3 * k + 7)) :=
    mem_nvis_iff.2 ⟨⟨by omega, by omega⟩, rfl⟩
  obtain ⟨hlt1, hlo1s, -, hhi1n, hclo1, hchi1⟩ := dbl_chord hs1
  obtain ⟨hlt2, hlo2s, -, hhi2n, hclo2, hchi2⟩ := dbl_chord hs2
  have hhi1ge : 3 * k + 6 ≤ dblHi k c (c (3 * k + 6)) := le_dblHi hs1nv
  have hhi2ge : 3 * k + 7 ≤ dblHi k c (c (3 * k + 7)) := le_dblHi hs2nv
  have hne12 : c (3 * k + 6) ≠ c (3 * k + 7) := fun h => positions_u1_ne_u2 hk huaw Str h
  have hHi1 : dblHi k c (c (3 * k + 6)) = 3 * k + 6 := by
    by_contra hcon
    have h7 : dblHi k c (c (3 * k + 6)) = 3 * k + 7 := by omega
    exact hne12 (by rw [← h7]; exact hchi1.symm)
  have hdisj : Disjoint (puDbl k c)
      ((narrowDbl k c).filter (fun s => 3 * k + 6 ≤ dblHi k c s)) :=
    Finset.disjoint_left.2 (fun s hsp hsn =>
      Finset.disjoint_left.1 disj_narrow_wide (Finset.mem_filter.1 hsn).1
        (puDbl_subset_wide hsp))
  have hunion : puDbl k c ∪ (narrowDbl k c).filter (fun s => 3 * k + 6 ≤ dblHi k c s)
      = {c (3 * k + 6), c (3 * k + 7)} := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro s hsm
      have hd : 3 * k + 6 ≤ dblHi k c s ∧ s ∈ twiceSet k c := by
        rcases Finset.mem_union.1 hsm with h | h
        · exact ⟨(Finset.mem_filter.1 h).2, wideDbl_subset_twice (Finset.mem_filter.1 h).1⟩
        · exact ⟨(Finset.mem_filter.1 h).2,
            (Finset.mem_filter.1 (Finset.mem_filter.1 h).1).1⟩
      obtain ⟨-, -, -, hhin, -, hchi⟩ := dbl_chord hd.2
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases (by omega : dblHi k c s = 3 * k + 6 ∨ dblHi k c s = 3 * k + 7) with h | h
      · exact Or.inl (by rw [← h, hchi])
      · exact Or.inr (by rw [← h, hchi])
    · intro s hsm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hsm
      rw [Finset.mem_union]
      rcases hsm with h | h
      · subst h
        rcases hlo1s with hl | hl
        · exact Or.inl (Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hs1, hl, by omega⟩,
            by omega⟩)
        · exact Or.inr (Finset.mem_filter.2
            ⟨Finset.mem_filter.2 ⟨hs1, Or.inr hl⟩, by omega⟩)
      · subst h
        rcases hlo2s with hl | hl
        · exact Or.inl (Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hs2, hl, by omega⟩,
            by omega⟩)
        · exact Or.inr (Finset.mem_filter.2
            ⟨Finset.mem_filter.2 ⟨hs2, Or.inr hl⟩, by omega⟩)
  have hcards := Finset.card_union_of_disjoint hdisj
  rw [hunion, Finset.card_insert_of_notMem (by simpa using hne12),
    Finset.card_singleton] at hcards
  omega

/-- **Proposition 6.5 (`prop:ell4`)**: the shape `ℓ = 4`, `d₀ ∈ {1,3}`, `b₁ = s₀ = 0` is
impossible.  Step 1 shows that there is at most one narrow chord and that its length is
`7` or `9`; Step 2 counts the loose visits by position and reaches a contradiction. -/
theorem ell4 (hk : 18 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) (hell : Str.ell = 4) (hd : Str.d0 = 1 ∨ Str.d0 = 3)
    (hb : bridgeCount k c = 0) (hs0 : singleCount k c = 0)
    {i0 : ℕ} (hi0 : i0 < k) (halign0 : c i0 = c (2 * k + 6 + i0)) : False := by
  classical
  have hk3 : (3 : ℕ) ≤ k := by omega
  have hadd := Str.d0_add
  have htl : 20 ≤ Str.tt * Str.ell := by omega
  have htlk : k ≤ Str.tt * Str.ell := by omega
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
  have h12 : i1 ≤ i2 := hlb _ hi2
  -- at most three narrow chords (Lemma 5.6(a),(c), `lem:narrow`)
  have hN3 : (narrowDbl k c).card ≤ 3 := by
    have := narrowDbl_card_le hk huaw Str (by omega)
    omega
  -- the four tallies of the loose visits
  have hT1 := count_prefix_left hk3 huaw hb hs0 hi1 hi2 hlb hI
  have hT2 := count_prefix_right hk3 huaw hb hs0 hi1 hi2 hlb hub hI
  have hT3 := count_tail_left hk3 huaw hb hs0 hi1 hi2 hlb hI
  have hT4 := count_tail_right hk3 huaw hb hs0 hi1 hi2 hlb hub hI
  have hg : (gammaDbl k c i1).card ≤ 3 := by
    have := gammaDbl_card_le hk huaw Str (by omega) hi1 hi2 hlb
    omega
  have hdd : (deltaDbl k c i2).card ≤ 3 := by
    have := deltaDbl_card_le hk huaw Str (by omega) hi1 hub
    omega
  -- `β ≤ 9` and `r ≤ 9`
  have hb9 : i1 ≤ 9 := by
    have h1 := Finset.card_filter_le (narrowDbl k c)
      (fun s => 2 * k + 6 ≤ dblLo k c s ∧ dblLo k c s < 2 * k + 6 + i1)
    have h2 := Finset.card_filter_le (narrowDbl k c)
      (fun s => 2 * k + 6 ≤ dblHi k c s ∧ dblHi k c s < 2 * k + 6 + i1)
    omega
  have hr9 : k - 1 - i2 ≤ 9 := by
    have h1 := Finset.card_filter_le (narrowDbl k c)
      (fun s => i2 < dblLo k c s ∧ dblLo k c s < k)
    have h2 := Finset.card_filter_le (narrowDbl k c)
      (fun s => i2 < dblHi k c s ∧ dblHi k c s < k)
    omega
  -- `PU + TU = 2`
  have hU := pu_tu_count hk3 huaw Str hb hs0
  -- Step 1: every narrow chord has length `7` or `9`, and there is at most one
  have hlen : ∀ s ∈ narrowDbl k c, dblHi k c s - dblLo k c s = 7 ∨
      dblHi k c s - dblLo k c s = 9 := by
    intro s hs
    refine narrow_len_seven_or_nine hk3 huaw Str hell htl hs ?_
    obtain ⟨-, -, -, hhin, -, -⟩ := dbl_chord (Finset.mem_filter.1 hs).1
    rcases narrow_type hk3 huaw Str hi1 hi2 h12 hI hs with h | h | h | h | h <;> omega
  have hN1 := narrow_card_le_one hk3 huaw Str hell htl htlk hlen
  -- Step 2: the counting contradiction
  rcases (by omega : (narrowDbl k c).card = 0 ∨ (narrowDbl k c).card = 1) with h0 | h1
  · have hemp : narrowDbl k c = ∅ := Finset.card_eq_zero.1 h0
    rw [hemp] at hT1 hT2 hT3 hT4 hU
    simp only [Finset.filter_empty, Finset.card_empty] at hT1 hT2 hT3 hT4 hU
    omega
  · obtain ⟨s, hsN⟩ := Finset.card_eq_one.1 h1
    have hsmem : s ∈ narrowDbl k c := by rw [hsN]; exact Finset.mem_singleton_self s
    have htype := narrow_type hk3 huaw Str hi1 hi2 h12 hI hsmem
    have hlens := hlen s hsmem
    obtain ⟨hlt, -, -, hhin, -, -⟩ := dbl_chord (Finset.mem_filter.1 hsmem).1
    rw [hsN] at hT1 hT2 hT3 hT4 hU
    simp only [Finset.filter_singleton, apply_ite Finset.card, Finset.card_singleton,
      Finset.card_empty] at hT1 hT2 hT3 hT4 hU
    rcases htype with h | h | h | h | h
    · -- a `PP`-chord with both indices in `J_L`: `β = γ + PU + 2` and `β = δ = r = γ`
      rw [if_pos (by omega), if_pos (by omega)] at hT1
      rw [if_neg (by omega), if_neg (by omega)] at hT2
      rw [if_neg (by omega), if_neg (by omega)] at hT3
      rw [if_neg (by omega), if_neg (by omega)] at hT4
      rw [if_neg (by omega)] at hU
      omega
    · -- a `PP`-chord with both indices in `J_R`
      rw [if_neg (by omega), if_neg (by omega)] at hT1
      rw [if_pos (by omega), if_pos (by omega)] at hT2
      rw [if_neg (by omega), if_neg (by omega)] at hT3
      rw [if_neg (by omega), if_neg (by omega)] at hT4
      rw [if_neg (by omega)] at hU
      omega
    · -- a `TT`-chord with both indices in `J_L`: then `β = δ + 2 = γ + 2` and `λ ≤ β - 1`
      rw [if_neg (by omega), if_neg (by omega)] at hT1
      rw [if_neg (by omega), if_neg (by omega)] at hT2
      rw [if_pos (by omega), if_pos (by omega)] at hT3
      rw [if_neg (by omega), if_neg (by omega)] at hT4
      rw [if_neg (by omega)] at hU
      omega
    · -- a `TT`-chord with both indices in `J_R`: then `r = γ + 2` and `λ ≤ r - 1`
      rw [if_neg (by omega), if_neg (by omega)] at hT1
      rw [if_neg (by omega), if_neg (by omega)] at hT2
      rw [if_neg (by omega), if_neg (by omega)] at hT3
      rw [if_pos (by omega), if_pos (by omega)] at hT4
      rw [if_neg (by omega)] at hU
      omega
    · -- a `TU`-chord: then `PU = 1`, `r = γ + 1` and `λ ≤ r + 1`
      rw [if_neg (by omega), if_neg (by omega)] at hT1
      rw [if_neg (by omega), if_neg (by omega)] at hT2
      rw [if_neg (by omega), if_neg (by omega)] at hT3
      rw [if_pos (by omega), if_neg (by omega)] at hT4
      rw [if_pos (by omega)] at hU
      omega

end

end AneVsAn
