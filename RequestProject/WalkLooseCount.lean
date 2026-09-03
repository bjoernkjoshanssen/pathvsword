import RequestProject.WalkBridgeParity

/-!
# Counting the loose visits (Section 6 of `ane-vs-an-separation-v4_1.tex`)

This file formalizes the bookkeeping that Step 2 of the proof of Proposition 6.5
(`prop:ell4`) sets up and that the proof of Proposition 6.7 (`prop:ell2clean`) reuses.

Throughout, `b₁ = s₀ = 0`, so every non-run time is a visit of a *double*, and the
"loose visits" of the source — the visits at a prefix time with broken index, at a tail
time with broken index, or at one of the two times `3k+6`, `n` of `u₁, u₂` — are exactly
the `2 b^# + 2` visits of the non-aligned doubles.

The key device is `loose_card_split`: for any set `A` of non-run times,
`|A| = |{doubles whose chord starts in A}| + |{doubles whose chord ends in A}|`.
Applying it to the four index blocks

* `PL = [0, i₁)` (prefix times with index in `J_L`),
* `PR = [i₂+1, k)` (prefix times with index in `J_R`),
* `TL = [2k+6, 2k+6+i₁)` (tail times with index in `J_L`),
* `TR = [2k+6+i₂+1, 3k+6)` (tail times with index in `J_R`),

and identifying the resulting sets of doubles through Lemma 5.10 (`lem:positions`) yields
the four tallies

```
β = 2 PP + PU + γ + δ,   r = 2 PP' + δ,   β = 2 TT + δ,   r = 2 TT' + TU + γ
```

of the source, in the form `count_prefix_left`, `count_prefix_right`, `count_tail_left`
and `count_tail_right`.
-/

namespace AneVsAn

set_option autoImplicit false

section

variable {k : ℕ} {S : Type} [DecidableEq S] {c : ℕ → S}

/-- The two non-run visits of a double are exactly the two endpoints of its chord
(Section 5.1, `sec:budget`). -/
theorem nvis_eq_pair {s : S} (hs : s ∈ twiceSet k c) :
    nvis k c s = {dblLo k c s, dblHi k c s} := by
  classical
  have hne := dbl_nvis_nonempty hs
  obtain ⟨hlt, -, -, -, -, -⟩ := dbl_chord hs
  have hsub : ({dblLo k c s, dblHi k c s} : Finset ℕ) ⊆ nvis k c s := by
    intro t ht
    rcases Finset.mem_insert.1 ht with h | h
    · rw [h]; exact dblLo_mem hne
    · rw [Finset.mem_singleton.1 h]; exact dblHi_mem hne
  have hc2 : ({dblLo k c s, dblHi k c s} : Finset ℕ).card = 2 :=
    Finset.card_pair (by omega)
  have hcs : (nvis k c s).card = 2 := (Finset.mem_filter.1 hs).2
  exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

/-- With no bridges and no singletons (`b₁ = s₀ = 0`) every non-run time is a visit of a
double.  This is the first sentence of Step 2 of the proof of Proposition 6.5
(`prop:ell4`). -/
theorem nonrun_double (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (hb : bridgeCount k c = 0) (hs0 : singleCount k c = 0)
    {t : ℕ} (ht : t ∈ nonRunTimes k) : c t ∈ twiceSet k c := by
  classical
  have htt : t ∈ times k := by
    simp only [nonRunTimes, Finset.mem_sdiff] at ht
    exact ht.1
  have hst : c t ∈ states k c := mem_states htt
  have hmem : t ∈ nvis k c (c t) := Finset.mem_filter.2 ⟨ht, rfl⟩
  have hpos : 0 < (nvis k c (c t)).card := Finset.card_pos.2 ⟨t, hmem⟩
  have hle := nvis_card_le_two hk huaw (c t)
  rcases (by omega : (nvis k c (c t)).card = 1 ∨ (nvis k c (c t)).card = 2) with h | h
  · exfalso
    have hmemo : c t ∈ onceSet k c := Finset.mem_filter.2 ⟨hst, h⟩
    have hco := card_onceSet hk huaw
    have := Finset.card_pos.2 ⟨_, hmemo⟩
    omega
  · exact Finset.mem_filter.2 ⟨hst, h⟩

/-- The doubles whose chord *starts* in `A`. -/
def looseLo (k : ℕ) (c : ℕ → S) (A : Finset ℕ) : Finset S :=
  (twiceSet k c).filter (fun s => dblLo k c s ∈ A)

/-- The doubles whose chord *ends* in `A`. -/
def looseHi (k : ℕ) (c : ℕ → S) (A : Finset ℕ) : Finset S :=
  (twiceSet k c).filter (fun s => dblHi k c s ∈ A)

/-- **The loose-visit count.**  If `b₁ = s₀ = 0`, then every set `A` of non-run times is
partitioned by the chords of the doubles: each double contributes one to `|A|` for each
endpoint of its chord lying in `A`.  This is the counting device of Step 2 of the proof of
Proposition 6.5 (`prop:ell4`). -/
theorem loose_card_split (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (hb : bridgeCount k c = 0) (hs0 : singleCount k c = 0)
    {A : Finset ℕ} (hA : A ⊆ nonRunTimes k) :
    A.card = (looseLo k c A).card + (looseHi k c A).card := by
  classical
  have hfib : A.card = ∑ s ∈ twiceSet k c, (A.filter (fun t => c t = s)).card :=
    Finset.card_eq_sum_card_fiberwise
      (fun t ht => nonrun_double hk huaw hb hs0 (hA ht))
  have hterm : ∀ s ∈ twiceSet k c, (A.filter (fun t => c t = s)).card =
      (if dblLo k c s ∈ A then 1 else 0) + (if dblHi k c s ∈ A then 1 else 0) := by
    intro s hs
    obtain ⟨hlt, -, -, -, -, -⟩ := dbl_chord hs
    have hset : A.filter (fun t => c t = s)
        = ({dblLo k c s, dblHi k c s} : Finset ℕ).filter (fun t => t ∈ A) := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨htA, hct⟩
        have : t ∈ nvis k c s := Finset.mem_filter.2 ⟨hA htA, hct⟩
        rw [nvis_eq_pair hs] at this
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        exact ⟨this, htA⟩
      · rintro ⟨ht, htA⟩
        refine ⟨htA, ?_⟩
        have hne := dbl_nvis_nonempty hs
        rcases ht with h | h
        · rw [h]; exact (Finset.mem_filter.1 (dblLo_mem hne)).2
        · rw [h]; exact (Finset.mem_filter.1 (dblHi_mem hne)).2
    rw [hset, Finset.filter_insert, Finset.filter_singleton]
    by_cases h1 : dblLo k c s ∈ A <;> by_cases h2 : dblHi k c s ∈ A <;>
      simp [h1, h2, Finset.card_insert_of_notMem, show dblLo k c s ≠ dblHi k c s by omega]
  rw [hfib, Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
    ← Finset.card_filter, ← Finset.card_filter]
  rfl

/-!
### The five kinds of doubles

Every double is aligned, narrow, a `γ`-double, a `δ`-double or a `PU`-double
(Lemma 5.10, `lem:positions`), and the five classes are pairwise disjoint.
-/

theorem gammaDbl_subset_wide {i1 : ℕ} : gammaDbl k c i1 ⊆ wideDbl k c :=
  Finset.filter_subset _ _

theorem deltaDbl_subset_wide {i2 : ℕ} : deltaDbl k c i2 ⊆ wideDbl k c :=
  Finset.filter_subset _ _

theorem puDbl_subset_wide : puDbl k c ⊆ wideDbl k c := Finset.filter_subset _ _

theorem alignedDbl_subset_wide : alignedDbl k c ⊆ wideDbl k c := Finset.filter_subset _ _

theorem wideDbl_subset_twice : wideDbl k c ⊆ twiceSet k c := Finset.filter_subset _ _

theorem narrowDbl_subset_twice : narrowDbl k c ⊆ twiceSet k c := Finset.filter_subset _ _

theorem disj_narrow_wide : Disjoint (narrowDbl k c) (wideDbl k c) := by
  refine Finset.disjoint_left.2 ?_
  intro s hs hw
  rw [narrowDbl, Finset.mem_filter] at hs
  rw [wideDbl, Finset.mem_filter] at hw
  rcases hs.2 with h | h <;> omega

/-- The positional facts attached to a `γ`-double: its prefix index lies in `J_L` and its
tail index in `J_R` (Lemma 5.10(a), `lem:positions`). -/
theorem gammaDbl_pos (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c) {i1 i2 : ℕ}
    (hi1 : i1 ∈ alignedSet k c)
    (hI : ∀ t, i1 ≤ t → t ≤ i2 → t ∈ alignedSet k c)
    {s : S} (hs : s ∈ gammaDbl k c i1) :
    dblLo k c s < i1 ∧ dblLo k c s < k ∧ 2 * k + 6 ≤ dblHi k c s ∧
      dblHi k c s ≤ 3 * k + 5 ∧ 2 * k + 6 + i2 < dblHi k c s := by
  rw [gammaDbl, Finset.mem_filter] at hs
  obtain ⟨hw, hhi5, hna, hlo1⟩ := hs
  obtain ⟨hlok, hhige, -, hclo, hchi⟩ := wideDbl_facts hw
  obtain ⟨-, hj'⟩ := wide_nonaligned_notMem hk huaw hw hhi5 hna
  obtain ⟨hi1k, hi1al⟩ := mem_alignedSet.1 hi1
  refine ⟨hlo1, hlok, hhige, hhi5, ?_⟩
  have hj'k : dblHi k c s - (2 * k + 6) < k := by omega
  have hwide : c (dblLo k c s) = c (2 * k + 6 + (dblHi k c s - (2 * k + 6))) := by
    rw [show 2 * k + 6 + (dblHi k c s - (2 * k + 6)) = dblHi k c s by omega, hclo, hchi]
  have hne : dblLo k c s ≠ dblHi k c s - (2 * k + 6) := by
    intro h; exact hna (by omega)
  have hnotlow : ¬ (dblHi k c s - (2 * k + 6) < i1) := fun h =>
    positions_wide_not_below hk huaw (i := i1) (j := dblLo k c s)
      (j' := dblHi k c s - (2 * k + 6)) hi1k hi1al hlo1 h hne hwide
  have hnotmid : ¬ (dblHi k c s - (2 * k + 6) ≤ i2) := fun h =>
    hj' (hI _ (by omega) h)
  omega

/-- The positional facts attached to a `δ`-double: its prefix index lies in `J_R` and its
tail index in `J_L` (Lemma 5.10(a), `lem:positions`). -/
theorem deltaDbl_pos (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c) {i1 i2 : ℕ}
    (hi2 : i2 ∈ alignedSet k c)
    (hI : ∀ t, i1 ≤ t → t ≤ i2 → t ∈ alignedSet k c)
    {s : S} (hs : s ∈ deltaDbl k c i2) :
    i2 < dblLo k c s ∧ dblLo k c s < k ∧ 2 * k + 6 ≤ dblHi k c s ∧
      dblHi k c s < 2 * k + 6 + i1 := by
  rw [deltaDbl, Finset.mem_filter] at hs
  obtain ⟨hw, hhi5, hna, hlo2⟩ := hs
  obtain ⟨hlok, hhige, -, hclo, hchi⟩ := wideDbl_facts hw
  obtain ⟨-, hj'⟩ := wide_nonaligned_notMem hk huaw hw hhi5 hna
  obtain ⟨hi2k, hi2al⟩ := mem_alignedSet.1 hi2
  refine ⟨hlo2, hlok, hhige, ?_⟩
  have hj'k : dblHi k c s - (2 * k + 6) < k := by omega
  have hwide : c (dblLo k c s) = c (2 * k + 6 + (dblHi k c s - (2 * k + 6))) := by
    rw [show 2 * k + 6 + (dblHi k c s - (2 * k + 6)) = dblHi k c s by omega, hclo, hchi]
  have hne : dblLo k c s ≠ dblHi k c s - (2 * k + 6) := by
    intro h; exact hna (by omega)
  have hnothigh : ¬ (i2 < dblHi k c s - (2 * k + 6)) := fun h =>
    positions_wide_not_above hk huaw (i := i2) (j := dblLo k c s)
      (j' := dblHi k c s - (2 * k + 6)) hi2al hlo2 h hlok hj'k hne hwide
  have hnotmid : ¬ (i1 ≤ dblHi k c s - (2 * k + 6)) := fun h =>
    hj' (hI _ h (by omega))
  omega

/-- The positional fact attached to a `PU`-double: its prefix index lies in `J_L`
(Lemma 5.10(b), `lem:positions`). -/
theorem puDbl_pos (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c) {i1 : ℕ}
    (hi1 : i1 ∈ alignedSet k c) {s : S} (hs : s ∈ puDbl k c) :
    dblLo k c s < i1 ∧ 3 * k + 6 ≤ dblHi k c s ∧ dblHi k c s ≤ 3 * k + 7 := by
  rw [puDbl, Finset.mem_filter] at hs
  obtain ⟨hw, hhi⟩ := hs
  obtain ⟨hlok, -, hhin, hclo, hchi⟩ := wideDbl_facts hw
  obtain ⟨hi1k, hi1al⟩ := mem_alignedSet.1 hi1
  refine ⟨?_, hhi, hhin⟩
  have hne := dbl_nvis_nonempty (Finset.mem_filter.1 hw).1
  rcases Nat.lt_trichotomy (dblLo k c s) i1 with h | h | h
  · exact h
  · exfalso
    refine no_three_nvis hk huaw (s := s) (x := dblLo k c s) (y := 2 * k + 6 + i1)
      (z := dblHi k c s) (dblLo_mem hne) ?_ (dblHi_mem hne) (by omega) (by omega) (by omega)
    exact mem_nvis_iff.2 ⟨⟨by omega, by omega⟩, by rw [← hi1al, ← h, hclo]⟩
  · exact absurd (positions_PU hk huaw (i := i1) (j := dblLo k c s) (v := dblHi k c s)
      hi1al h hlok (by omega) (by rw [hclo, hchi])) (fun h => h.elim)

/-- The prefix index of an aligned double is an aligned index. -/
theorem alignedDbl_lo_mem {s : S} (hs : s ∈ alignedDbl k c) :
    dblLo k c s ∈ alignedSet k c := by
  rw [alignedDbl, Finset.mem_filter] at hs
  obtain ⟨hw, hal⟩ := hs
  obtain ⟨hlok, -, -, hclo, hchi⟩ := wideDbl_facts hw
  exact mem_alignedSet.2 ⟨hlok, by rw [hclo, ← hal, hchi]⟩

/-- **Lemma 5.10 (`lem:positions`)**, in the form used by the count: every double is
aligned, narrow, a `γ`-double, a `δ`-double or a `PU`-double. -/
theorem dbl_class (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c) {i1 i2 : ℕ}
    (hI : ∀ t, i1 ≤ t → t ≤ i2 → t ∈ alignedSet k c) {s : S} (hs : s ∈ twiceSet k c) :
    s ∈ narrowDbl k c ∨ s ∈ alignedDbl k c ∨ s ∈ gammaDbl k c i1 ∨
      s ∈ deltaDbl k c i2 ∨ s ∈ puDbl k c := by
  rcases Finset.mem_union.1 (twiceSet_subset_union hs) with h | h
  · exact Or.inl h
  · have := wideDbl_subset hk huaw hI h
    simp only [Finset.mem_union] at this
    tauto

theorem disj_gamma_pu {i1 : ℕ} : Disjoint (gammaDbl k c i1) (puDbl k c) := by
  refine Finset.disjoint_left.2 ?_
  intro s hs hp
  rw [gammaDbl, Finset.mem_filter] at hs
  rw [puDbl, Finset.mem_filter] at hp
  omega

theorem disj_delta_pu {i2 : ℕ} : Disjoint (deltaDbl k c i2) (puDbl k c) := by
  refine Finset.disjoint_left.2 ?_
  intro s hs hp
  rw [deltaDbl, Finset.mem_filter] at hs
  rw [puDbl, Finset.mem_filter] at hp
  omega

/-!
### The four tallies of the loose visits
-/

/-- **The first tally**: counting the loose prefix visits with index in `J_L`, i.e.
`β = 2 PP_L + PU + γ` in the notation of Step 2 of the proof of Proposition 6.5
(`prop:ell4`).  Here `PP_L` is split into the two contributions of the two endpoints. -/
theorem count_prefix_left (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (hb : bridgeCount k c = 0) (hs0 : singleCount k c = 0) {i1 i2 : ℕ}
    (hi1 : i1 ∈ alignedSet k c) (hi2 : i2 ∈ alignedSet k c)
    (hlb : ∀ t ∈ alignedSet k c, i1 ≤ t)
    (hI : ∀ t, i1 ≤ t → t ≤ i2 → t ∈ alignedSet k c) :
    i1 = ((narrowDbl k c).filter (fun s => dblLo k c s < i1)).card
      + (gammaDbl k c i1).card + (puDbl k c).card
      + ((narrowDbl k c).filter (fun s => dblHi k c s < i1)).card := by
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
  have hsplit := loose_card_split hk huaw hb hs0 hAsub
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

/-- **The second tally**: counting the loose prefix visits with index in `J_R`, i.e.
`r = 2 PP_R + δ`. -/
theorem count_prefix_right (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (hb : bridgeCount k c = 0) (hs0 : singleCount k c = 0) {i1 i2 : ℕ}
    (hi1 : i1 ∈ alignedSet k c) (hi2 : i2 ∈ alignedSet k c)
    (hlb : ∀ t ∈ alignedSet k c, i1 ≤ t) (hub : ∀ t ∈ alignedSet k c, t ≤ i2)
    (hI : ∀ t, i1 ≤ t → t ≤ i2 → t ∈ alignedSet k c) :
    k - 1 - i2 = ((narrowDbl k c).filter (fun s => i2 < dblLo k c s ∧ dblLo k c s < k)).card
      + (deltaDbl k c i2).card
      + ((narrowDbl k c).filter (fun s => i2 < dblHi k c s ∧ dblHi k c s < k)).card := by
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
  have hsplit := loose_card_split hk huaw hb hs0 hAsub
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

/-- **The third tally**: counting the loose tail visits with index in `J_L`, i.e.
`β = 2 TT_L + δ`. -/
theorem count_tail_left (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (hb : bridgeCount k c = 0) (hs0 : singleCount k c = 0) {i1 i2 : ℕ}
    (hi1 : i1 ∈ alignedSet k c) (hi2 : i2 ∈ alignedSet k c)
    (hlb : ∀ t ∈ alignedSet k c, i1 ≤ t)
    (hI : ∀ t, i1 ≤ t → t ≤ i2 → t ∈ alignedSet k c) :
    i1 = ((narrowDbl k c).filter
          (fun s => 2 * k + 6 ≤ dblLo k c s ∧ dblLo k c s < 2 * k + 6 + i1)).card
      + ((narrowDbl k c).filter
          (fun s => 2 * k + 6 ≤ dblHi k c s ∧ dblHi k c s < 2 * k + 6 + i1)).card
      + (deltaDbl k c i2).card := by
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
  have hsplit := loose_card_split hk huaw hb hs0 hAsub
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

/-- **The fourth tally**: counting the loose tail visits with index in `J_R`, i.e.
`r = 2 TT_R + TU + γ`. -/
theorem count_tail_right (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (hb : bridgeCount k c = 0) (hs0 : singleCount k c = 0) {i1 i2 : ℕ}
    (hi1 : i1 ∈ alignedSet k c) (hi2 : i2 ∈ alignedSet k c)
    (hlb : ∀ t ∈ alignedSet k c, i1 ≤ t) (hub : ∀ t ∈ alignedSet k c, t ≤ i2)
    (hI : ∀ t, i1 ≤ t → t ≤ i2 → t ∈ alignedSet k c) :
    k - 1 - i2 = ((narrowDbl k c).filter
          (fun s => 2 * k + 6 + i2 < dblLo k c s ∧ dblLo k c s < 3 * k + 6)).card
      + ((narrowDbl k c).filter
          (fun s => 2 * k + 6 + i2 < dblHi k c s ∧ dblHi k c s < 3 * k + 6)).card
      + (gammaDbl k c i1).card := by
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
  have hsplit := loose_card_split hk huaw hb hs0 hAsub
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
