import RequestProject.WalkLooseCount

/-!
# Counting the loose visits in the presence of bridges (Section 6 of
`ane-vs-an-separation-v4_1.tex`)

`RequestProject/WalkLooseCount.lean` counts the loose visits under the hypothesis
`b₁ = s₀ = 0`, i.e. when every non-run time is a visit of a double.  Step 1 of the proof
of Proposition 6.8 (`prop:ell2bridge`) needs the same bookkeeping in the *bridge shape*,
where `b₁ = s₀ = 1`: there each non-run time is a visit of a double **or** the single
non-run visit of a state with only one non-run visit (a bridge or a singleton).

This file provides

* `onceIn` — the states with a single non-run visit, that visit lying in a prescribed set
  of times;
* `loose_card_split_gen` — the counting device
  `|A| = |{doubles starting in A}| + |{doubles ending in A}| + |{once-states visiting A}|`;
* `count_prefix_left_gen`, `count_prefix_right_gen`, `count_tail_left_gen`,
  `count_tail_right_gen` — the four tallies
  `β = 1 + γ`, `r = δ + [pb]`, `β = δ + [tb]`, `r = γ`
  of Step 1 of the proof of Proposition 6.8 (`prop:ell2bridge`), in the form which still
  displays the (here empty) contributions of the narrow chords and the contribution of
  the once-states.
-/

namespace AneVsAn

set_option autoImplicit false

section

variable {k : ℕ} {S : Type} [DecidableEq S] {c : ℕ → S}

/-- The states with exactly one non-run visit whose visit lies in `A`.  In the bridge
shape of Proposition 6.8 (`prop:ell2bridge`) these are the bridge `y` and the singleton,
counted when their unique non-run visit falls in the block `A`. -/
def onceIn (k : ℕ) (c : ℕ → S) (A : Finset ℕ) : Finset S :=
  (onceSet k c).filter (fun s => dblLo k c s ∈ A)

/-- The unique non-run visit of a state of `onceSet` is `dblLo`. -/
theorem once_nvis_eq {s : S} (hs : s ∈ onceSet k c) :
    nvis k c s = {dblLo k c s} := by
  classical
  simp only [onceSet, Finset.mem_filter] at hs
  obtain ⟨x, hx⟩ := Finset.card_eq_one.1 hs.2
  have hne : (nvis k c s).Nonempty := ⟨x, by rw [hx]; exact Finset.mem_singleton_self x⟩
  have hmem := dblLo_mem hne
  rw [hx, Finset.mem_singleton] at hmem
  rw [hx, hmem]

/-- **The loose-visit count in the presence of bridges.**  Every set `A` of non-run times
is partitioned by the chords of the doubles and by the single non-run visits of the
once-states.  This is the counting device of Step 1 of the proof of Proposition 6.8
(`prop:ell2bridge`). -/
theorem loose_card_split_gen (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    {A : Finset ℕ} (hA : A ⊆ nonRunTimes k) :
    A.card = (looseLo k c A).card + (looseHi k c A).card + (onceIn k c A).card := by
  classical
  have hmemtimes : ∀ t ∈ A, t ∈ times k := by
    intro t ht
    have := hA ht
    simp only [nonRunTimes, Finset.mem_sdiff] at this
    exact this.1
  have hfib : A.card = ∑ s ∈ states k c, (A.filter (fun t => c t = s)).card :=
    Finset.card_eq_sum_card_fiberwise (fun t ht => mem_states (hmemtimes t ht))
  rw [hfib, sum_split hk huaw]
  have hcl : ∀ s ∈ cluster k c, (A.filter (fun t => c t = s)).card = 0 := by
    intro s hs
    simp only [cluster, Finset.mem_filter] at hs
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro t ht hct
    have hmem : t ∈ nvis k c s := Finset.mem_filter.2 ⟨hA ht, hct⟩
    have := Finset.card_pos.2 ⟨t, hmem⟩
    omega
  have honce : ∀ s ∈ onceSet k c, (A.filter (fun t => c t = s)).card
      = if dblLo k c s ∈ A then 1 else 0 := by
    intro s hs
    have hnv := once_nvis_eq hs
    have hset : A.filter (fun t => c t = s) = A.filter (fun t => t = dblLo k c s) := by
      ext t
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨htA, hct⟩
        refine ⟨htA, ?_⟩
        have hmem : t ∈ nvis k c s := Finset.mem_filter.2 ⟨hA htA, hct⟩
        rw [hnv, Finset.mem_singleton] at hmem
        exact hmem
      · rintro ⟨htA, rfl⟩
        refine ⟨htA, ?_⟩
        have hmem : dblLo k c s ∈ nvis k c s := by rw [hnv]; exact Finset.mem_singleton_self _
        exact (Finset.mem_filter.1 hmem).2
    rw [hset, Finset.filter_eq']
    split <;> simp
  have htwice : ∀ s ∈ twiceSet k c, (A.filter (fun t => c t = s)).card =
      (if dblLo k c s ∈ A then 1 else 0) + (if dblHi k c s ∈ A then 1 else 0) := by
    intro s hs
    obtain ⟨hlt, -, -, -, -, -⟩ := dbl_chord hs
    have hset : A.filter (fun t => c t = s)
        = ({dblLo k c s, dblHi k c s} : Finset ℕ).filter (fun t => t ∈ A) := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨htA, hct⟩
        have hmem : t ∈ nvis k c s := Finset.mem_filter.2 ⟨hA htA, hct⟩
        rw [nvis_eq_pair hs] at hmem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        exact ⟨hmem, htA⟩
      · rintro ⟨ht, htA⟩
        refine ⟨htA, ?_⟩
        have hne := dbl_nvis_nonempty hs
        rcases ht with h | h
        · rw [h]; exact (Finset.mem_filter.1 (dblLo_mem hne)).2
        · rw [h]; exact (Finset.mem_filter.1 (dblHi_mem hne)).2
    rw [hset, Finset.filter_insert, Finset.filter_singleton]
    by_cases h1 : dblLo k c s ∈ A <;> by_cases h2 : dblHi k c s ∈ A <;>
      simp [h1, h2, Finset.card_insert_of_notMem, show dblLo k c s ≠ dblHi k c s by omega]
  rw [Finset.sum_congr rfl hcl, Finset.sum_congr rfl honce, Finset.sum_congr rfl htwice,
    Finset.sum_add_distrib, ← Finset.card_filter, ← Finset.card_filter, ← Finset.card_filter]
  simp only [Finset.sum_const_zero]
  show _ = ((twiceSet k c).filter _).card + ((twiceSet k c).filter _).card
    + ((onceSet k c).filter _).card
  rw [← looseLo, ← looseHi, ← onceIn]
  omega

/-!
### The four tallies in the presence of bridges

These are the analogues of `count_prefix_left`, `count_prefix_right`, `count_tail_left`
and `count_tail_right` for the bridge shape: the same identities with the extra
contribution of the once-states.
-/

/-- **The first tally of Step 1 of Proposition 6.8 (`prop:ell2bridge`)**: counting the
loose prefix visits with index in `J_L`, i.e. `β = 1 + γ` once the narrow chords are known
to be absent and the `PU`-chord is the only once-state contribution. -/
theorem count_prefix_left_gen (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    {i1 i2 : ℕ} (hi1 : i1 ∈ alignedSet k c) (hi2 : i2 ∈ alignedSet k c)
    (hlb : ∀ t ∈ alignedSet k c, i1 ≤ t)
    (hI : ∀ t, i1 ≤ t → t ≤ i2 → t ∈ alignedSet k c) :
    i1 = ((narrowDbl k c).filter (fun s => dblLo k c s < i1)).card
      + (gammaDbl k c i1).card + (puDbl k c).card
      + ((narrowDbl k c).filter (fun s => dblHi k c s < i1)).card
      + (onceIn k c (Finset.range i1)).card := by
  classical
  have hi1k := (mem_alignedSet.1 hi1).1
  have hi2k := (mem_alignedSet.1 hi2).1
  have hi12 : i1 ≤ i2 := hlb _ hi2
  set A : Finset ℕ := Finset.range i1 with hA
  have hAsub : A ⊆ nonRunTimes k := by
    intro t ht
    rw [hA, Finset.mem_range] at ht
    simp only [nonRunTimes, times, runTimes, Finset.mem_sdiff, Finset.mem_range,
      Finset.mem_Icc]
    exact ⟨by omega, by omega⟩
  have hAcard : A.card = i1 := by simp [hA]
  have hsplit := loose_card_split_gen hk huaw hAsub
  have hhi : looseHi k c A = (narrowDbl k c).filter (fun s => dblHi k c s < i1) := by
    ext s
    simp only [looseHi, Finset.mem_filter, hA, Finset.mem_range, narrowDbl]
    constructor
    · rintro ⟨hs, hlt⟩
      obtain ⟨hltp, -, -, -, -, -⟩ := dbl_chord hs
      exact ⟨⟨hs, Or.inl (by omega)⟩, hlt⟩
    · rintro ⟨⟨hs, -⟩, hlt⟩
      exact ⟨hs, hlt⟩
  have hlo : looseLo k c A
      = ((narrowDbl k c).filter (fun s => dblLo k c s < i1) ∪ gammaDbl k c i1)
        ∪ puDbl k c := by
    ext s
    simp only [looseLo, Finset.mem_filter, hA, Finset.mem_range, Finset.mem_union, narrowDbl]
    constructor
    · rintro ⟨hs, hlt⟩
      rcases dbl_class hk huaw hI hs with h | h | h | h | h
      · exact Or.inl (Or.inl ⟨Finset.mem_filter.1 h, hlt⟩)
      · exact absurd (hlb _ (alignedDbl_lo_mem h)) (by omega)
      · exact Or.inl (Or.inr h)
      · obtain ⟨h1, -, -, -⟩ := deltaDbl_pos hk huaw hi2 hI h
        omega
      · exact Or.inr h
    · rintro (((⟨⟨hs, -⟩, hlt⟩) | h) | h)
      · exact ⟨hs, hlt⟩
      · exact ⟨wideDbl_subset_twice (gammaDbl_subset_wide h),
          (gammaDbl_pos (i2 := i2) hk huaw hi1 hI h).1⟩
      · exact ⟨wideDbl_subset_twice (puDbl_subset_wide h), (puDbl_pos hk huaw hi1 h).1⟩
  rw [hlo, hhi] at hsplit
  rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint] at hsplit
  · omega
  · exact Finset.disjoint_left.2 (fun s hs hg =>
      Finset.disjoint_left.1 disj_narrow_wide (Finset.mem_filter.1 hs).1
        (gammaDbl_subset_wide hg))
  · refine Finset.disjoint_left.2 ?_
    intro s hs hp
    rcases Finset.mem_union.1 hs with h | h
    · exact Finset.disjoint_left.1 disj_narrow_wide (Finset.mem_filter.1 h).1
        (puDbl_subset_wide hp)
    · exact Finset.disjoint_left.1 disj_gamma_pu h hp

/-- **The second tally of Step 1 of Proposition 6.8 (`prop:ell2bridge`)**: counting the
loose prefix visits with index in `J_R`, i.e. `r = δ + [pb]`. -/
theorem count_prefix_right_gen (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    {i1 i2 : ℕ} (hi1 : i1 ∈ alignedSet k c) (hi2 : i2 ∈ alignedSet k c)
    (hlb : ∀ t ∈ alignedSet k c, i1 ≤ t) (hub : ∀ t ∈ alignedSet k c, t ≤ i2)
    (hI : ∀ t, i1 ≤ t → t ≤ i2 → t ∈ alignedSet k c) :
    k - 1 - i2 = ((narrowDbl k c).filter (fun s => i2 < dblLo k c s ∧ dblLo k c s < k)).card
      + (deltaDbl k c i2).card
      + ((narrowDbl k c).filter (fun s => i2 < dblHi k c s ∧ dblHi k c s < k)).card
      + (onceIn k c (Finset.Ico (i2 + 1) k)).card := by
  classical
  have hi1k := (mem_alignedSet.1 hi1).1
  have hi2k := (mem_alignedSet.1 hi2).1
  have hi12 : i1 ≤ i2 := hlb _ hi2
  set A : Finset ℕ := Finset.Ico (i2 + 1) k with hA
  have hAsub : A ⊆ nonRunTimes k := by
    intro t ht
    rw [hA, Finset.mem_Ico] at ht
    simp only [nonRunTimes, times, runTimes, Finset.mem_sdiff, Finset.mem_range,
      Finset.mem_Icc]
    exact ⟨by omega, by omega⟩
  have hAcard : A.card = k - 1 - i2 := by rw [hA, Nat.card_Ico]; omega
  have hsplit := loose_card_split_gen hk huaw hAsub
  have hhi : looseHi k c A
      = (narrowDbl k c).filter (fun s => i2 < dblHi k c s ∧ dblHi k c s < k) := by
    ext s
    simp only [looseHi, Finset.mem_filter, hA, Finset.mem_Ico, narrowDbl]
    constructor
    · rintro ⟨hs, hlt⟩
      obtain ⟨hltp, -, -, -, -, -⟩ := dbl_chord hs
      exact ⟨⟨hs, Or.inl (by omega)⟩, by omega, by omega⟩
    · rintro ⟨⟨hs, -⟩, hlt⟩
      exact ⟨hs, by omega, by omega⟩
  have hlo : looseLo k c A
      = (narrowDbl k c).filter (fun s => i2 < dblLo k c s ∧ dblLo k c s < k)
        ∪ deltaDbl k c i2 := by
    ext s
    simp only [looseLo, Finset.mem_filter, hA, Finset.mem_Ico, Finset.mem_union, narrowDbl]
    constructor
    · rintro ⟨hs, hlt⟩
      rcases dbl_class hk huaw hI hs with h | h | h | h | h
      · exact Or.inl ⟨Finset.mem_filter.1 h, by omega, by omega⟩
      · exact absurd (hub _ (alignedDbl_lo_mem h)) (by omega)
      · obtain ⟨h1, -, -, -, -⟩ := gammaDbl_pos (i2 := i2) hk huaw hi1 hI h
        omega
      · exact Or.inr h
      · obtain ⟨h1, -, -⟩ := puDbl_pos hk huaw hi1 h
        omega
    · rintro ((⟨⟨hs, -⟩, hlt⟩) | h)
      · exact ⟨hs, by omega, by omega⟩
      · obtain ⟨h1, h2, -, -⟩ := deltaDbl_pos hk huaw hi2 hI h
        exact ⟨wideDbl_subset_twice (deltaDbl_subset_wide h), by omega, by omega⟩
  rw [hlo, hhi] at hsplit
  rw [Finset.card_union_of_disjoint] at hsplit
  · omega
  · exact Finset.disjoint_left.2 (fun s hs hg =>
      Finset.disjoint_left.1 disj_narrow_wide (Finset.mem_filter.1 hs).1
        (deltaDbl_subset_wide hg))

/-- **The third tally of Step 1 of Proposition 6.8 (`prop:ell2bridge`)**: counting the
loose tail visits with index in `J_L`, i.e. `β = δ + [tb]`. -/
theorem count_tail_left_gen (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    {i1 i2 : ℕ} (hi1 : i1 ∈ alignedSet k c) (hi2 : i2 ∈ alignedSet k c)
    (hlb : ∀ t ∈ alignedSet k c, i1 ≤ t)
    (hI : ∀ t, i1 ≤ t → t ≤ i2 → t ∈ alignedSet k c) :
    i1 = ((narrowDbl k c).filter
          (fun s => 2 * k + 6 ≤ dblLo k c s ∧ dblLo k c s < 2 * k + 6 + i1)).card
      + ((narrowDbl k c).filter
          (fun s => 2 * k + 6 ≤ dblHi k c s ∧ dblHi k c s < 2 * k + 6 + i1)).card
      + (deltaDbl k c i2).card
      + (onceIn k c (Finset.Ico (2 * k + 6) (2 * k + 6 + i1))).card := by
  classical
  have hi1k := (mem_alignedSet.1 hi1).1
  have hi2k := (mem_alignedSet.1 hi2).1
  have hi12 : i1 ≤ i2 := hlb _ hi2
  set A : Finset ℕ := Finset.Ico (2 * k + 6) (2 * k + 6 + i1) with hA
  have hAsub : A ⊆ nonRunTimes k := by
    intro t ht
    rw [hA, Finset.mem_Ico] at ht
    simp only [nonRunTimes, times, runTimes, Finset.mem_sdiff, Finset.mem_range,
      Finset.mem_Icc]
    exact ⟨by omega, by omega⟩
  have hAcard : A.card = i1 := by rw [hA, Nat.card_Ico]; omega
  have hsplit := loose_card_split_gen hk huaw hAsub
  have hlo : looseLo k c A = (narrowDbl k c).filter
      (fun s => 2 * k + 6 ≤ dblLo k c s ∧ dblLo k c s < 2 * k + 6 + i1) := by
    ext s
    simp only [looseLo, Finset.mem_filter, hA, Finset.mem_Ico, narrowDbl]
    constructor
    · rintro ⟨hs, hlt⟩
      exact ⟨⟨hs, Or.inr (by omega)⟩, hlt⟩
    · rintro ⟨⟨hs, -⟩, hlt⟩
      exact ⟨hs, hlt⟩
  have hhi : looseHi k c A
      = (narrowDbl k c).filter
          (fun s => 2 * k + 6 ≤ dblHi k c s ∧ dblHi k c s < 2 * k + 6 + i1)
        ∪ deltaDbl k c i2 := by
    ext s
    simp only [looseHi, Finset.mem_filter, hA, Finset.mem_Ico, Finset.mem_union, narrowDbl]
    constructor
    · rintro ⟨hs, hlt⟩
      rcases dbl_class hk huaw hI hs with h | h | h | h | h
      · exact Or.inl ⟨Finset.mem_filter.1 h, hlt⟩
      · have hal := alignedDbl_lo_mem h
        rw [alignedDbl, Finset.mem_filter] at h
        have := hlb _ hal
        omega
      · obtain ⟨-, -, -, -, h5⟩ := gammaDbl_pos (i2 := i2) hk huaw hi1 hI h
        omega
      · exact Or.inr h
      · obtain ⟨-, h2, -⟩ := puDbl_pos hk huaw hi1 h
        omega
    · rintro ((⟨⟨hs, -⟩, hlt⟩) | h)
      · exact ⟨hs, hlt⟩
      · obtain ⟨-, -, h3, h4⟩ := deltaDbl_pos hk huaw hi2 hI h
        exact ⟨wideDbl_subset_twice (deltaDbl_subset_wide h), h3, h4⟩
  rw [hlo, hhi] at hsplit
  rw [Finset.card_union_of_disjoint] at hsplit
  · omega
  · exact Finset.disjoint_left.2 (fun s hs hg =>
      Finset.disjoint_left.1 disj_narrow_wide (Finset.mem_filter.1 hs).1
        (deltaDbl_subset_wide hg))

/-- **The fourth tally of Step 1 of Proposition 6.8 (`prop:ell2bridge`)**: counting the
loose tail visits with index in `J_R`, i.e. `r = γ`. -/
theorem count_tail_right_gen (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    {i1 i2 : ℕ} (hi1 : i1 ∈ alignedSet k c) (hi2 : i2 ∈ alignedSet k c)
    (hlb : ∀ t ∈ alignedSet k c, i1 ≤ t) (hub : ∀ t ∈ alignedSet k c, t ≤ i2)
    (hI : ∀ t, i1 ≤ t → t ≤ i2 → t ∈ alignedSet k c) :
    k - 1 - i2 = ((narrowDbl k c).filter
          (fun s => 2 * k + 6 + i2 < dblLo k c s ∧ dblLo k c s < 3 * k + 6)).card
      + ((narrowDbl k c).filter
          (fun s => 2 * k + 6 + i2 < dblHi k c s ∧ dblHi k c s < 3 * k + 6)).card
      + (gammaDbl k c i1).card
      + (onceIn k c (Finset.Ico (2 * k + 6 + i2 + 1) (3 * k + 6))).card := by
  classical
  have hi1k := (mem_alignedSet.1 hi1).1
  have hi2k := (mem_alignedSet.1 hi2).1
  have hi12 : i1 ≤ i2 := hlb _ hi2
  set A : Finset ℕ := Finset.Ico (2 * k + 6 + i2 + 1) (3 * k + 6) with hA
  have hAsub : A ⊆ nonRunTimes k := by
    intro t ht
    rw [hA, Finset.mem_Ico] at ht
    simp only [nonRunTimes, times, runTimes, Finset.mem_sdiff, Finset.mem_range,
      Finset.mem_Icc]
    exact ⟨by omega, by omega⟩
  have hAcard : A.card = k - 1 - i2 := by rw [hA, Nat.card_Ico]; omega
  have hsplit := loose_card_split_gen hk huaw hAsub
  have hlo : looseLo k c A = (narrowDbl k c).filter
      (fun s => 2 * k + 6 + i2 < dblLo k c s ∧ dblLo k c s < 3 * k + 6) := by
    ext s
    simp only [looseLo, Finset.mem_filter, hA, Finset.mem_Ico, narrowDbl]
    constructor
    · rintro ⟨hs, hlt⟩
      exact ⟨⟨hs, Or.inr (by omega)⟩, by omega, by omega⟩
    · rintro ⟨⟨hs, -⟩, hlt⟩
      exact ⟨hs, by omega, by omega⟩
  have hhi : looseHi k c A
      = (narrowDbl k c).filter
          (fun s => 2 * k + 6 + i2 < dblHi k c s ∧ dblHi k c s < 3 * k + 6)
        ∪ gammaDbl k c i1 := by
    ext s
    simp only [looseHi, Finset.mem_filter, hA, Finset.mem_Ico, Finset.mem_union, narrowDbl]
    constructor
    · rintro ⟨hs, hlt⟩
      rcases dbl_class hk huaw hI hs with h | h | h | h | h
      · exact Or.inl ⟨Finset.mem_filter.1 h, by omega, by omega⟩
      · have hal := alignedDbl_lo_mem h
        rw [alignedDbl, Finset.mem_filter] at h
        have := hub _ hal
        omega
      · exact Or.inr h
      · obtain ⟨-, -, -, h4⟩ := deltaDbl_pos hk huaw hi2 hI h
        omega
      · obtain ⟨-, h2, -⟩ := puDbl_pos hk huaw hi1 h
        omega
    · rintro ((⟨⟨hs, -⟩, hlt⟩) | h)
      · exact ⟨hs, by omega, by omega⟩
      · obtain ⟨-, -, -, h4, h5⟩ := gammaDbl_pos (i2 := i2) hk huaw hi1 hI h
        exact ⟨wideDbl_subset_twice (gammaDbl_subset_wide h), by omega, by omega⟩
  rw [hlo, hhi] at hsplit
  rw [Finset.card_union_of_disjoint] at hsplit
  · omega
  · exact Finset.disjoint_left.2 (fun s hs hg =>
      Finset.disjoint_left.1 disj_narrow_wide (Finset.mem_filter.1 hs).1
        (gammaDbl_subset_wide hg))

end

end AneVsAn
