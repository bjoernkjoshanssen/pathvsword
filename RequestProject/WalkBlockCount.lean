import RequestProject.WalkAligned

/-!
# The aligned block and the count of the non-aligned chords (Lemma 5.12, `lem:counts`)

This file formalizes Section 5.4 (`sec:block`) of `ane-vs-an-separation-v4_1.tex`:

* the set `I = {i ≤ k-1 : g_i = h_i}` of *aligned* indices (`alignedSet`), which is an
  interval `[i₁,i₂]` by Lemma 4.6 (`lem:block`);
* the classification of the non-aligned doubles into `γ`-chords, `δ`-chords, `PU`-chords
  and narrow chords (Lemma 5.10, `lem:positions`);
* the resulting bound `b^# = k - |I| ≤ 3ℓ - 2 + (b₁+s₀)/2` of Lemma 5.12(c)
  (`lem:counts`); this is the version of the source's bound `b^# ≤ 4ℓ-3+(b₁+s₀)/2` that
  the present classification yields (the narrow prefix and narrow tail chords are counted
  together here, which saves one `ℓ-1`), and it gives the same numerical values
  `b^# ≤ 4` for `ℓ = 1` and `b^# ≤ 7` for `ℓ = 2`.
-/

namespace AneVsAn

set_option autoImplicit false

section

variable {k : ℕ} {S : Type} [DecidableEq S] {c : ℕ → S}

/-- The set `I` of *aligned* indices of Section 5.4 (`sec:block`):
`I = {i ≤ k-1 : g_i = h_i}`. -/
def alignedSet (k : ℕ) (c : ℕ → S) : Finset ℕ :=
  (Finset.range k).filter (fun i => c i = c (2 * k + 6 + i))

theorem mem_alignedSet {i : ℕ} :
    i ∈ alignedSet k c ↔ i < k ∧ c i = c (2 * k + 6 + i) := by
  simp [alignedSet, Finset.mem_filter, Finset.mem_range]

/-- The basic data attached to a wide double: its prefix index, its tail-side index, and
the fact that both carry the state. -/
theorem wideDbl_facts {s : S} (hs : s ∈ wideDbl k c) :
    dblLo k c s < k ∧ 2 * k + 6 ≤ dblHi k c s ∧ dblHi k c s ≤ 3 * k + 7 ∧
      c (dblLo k c s) = s ∧ c (dblHi k c s) = s := by
  rw [wideDbl, Finset.mem_filter] at hs
  obtain ⟨hst, hlo, hhi⟩ := hs
  obtain ⟨-, -, -, hhin, hclo, hchi⟩ := dbl_chord hst
  exact ⟨hlo, hhi, hhin, hclo, hchi⟩

/-- An aligned index gives a *double*, whose chord is the aligned wide chord
`(i, 2k+6+i)`. -/
theorem aligned_dbl (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    {i : ℕ} (hi : i ∈ alignedSet k c) :
    c i ∈ wideDbl k c ∧ dblLo k c (c i) = i ∧ dblHi k c (c i) = 2 * k + 6 + i := by
  rw [mem_alignedSet] at hi
  obtain ⟨hik, halign⟩ := hi
  have h1 : i ∈ nvis k c (c i) := by
    rw [mem_nvis_iff]; exact ⟨⟨by omega, by omega⟩, rfl⟩
  have h2 : 2 * k + 6 + i ∈ nvis k c (c i) := by
    rw [mem_nvis_iff]; exact ⟨⟨by omega, by omega⟩, halign.symm⟩
  have hsub : ({i, 2 * k + 6 + i} : Finset ℕ) ⊆ nvis k c (c i) := by
    intro t ht
    rcases Finset.mem_insert.1 ht with h | h
    · rw [h]; exact h1
    · rw [Finset.mem_singleton.1 h]; exact h2
  have hcard2 : ({i, 2 * k + 6 + i} : Finset ℕ).card = 2 := by
    exact Finset.card_pair (by omega)
  have hle := nvis_card_le_two hk huaw (c i)
  have heq : nvis k c (c i) = {i, 2 * k + 6 + i} :=
    (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  have hne : (nvis k c (c i)).Nonempty := ⟨i, h1⟩
  have hlo : dblLo k c (c i) = i := by
    have hm := dblLo_mem hne
    have hle' := dblLo_le h1
    rw [heq] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    omega
  have hhi : dblHi k c (c i) = 2 * k + 6 + i := by
    have hm := dblHi_mem hne
    have hle' := le_dblHi h2
    rw [heq] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    omega
  refine ⟨?_, hlo, hhi⟩
  rw [wideDbl, Finset.mem_filter]
  refine ⟨?_, by omega, by omega⟩
  rw [twiceSet, Finset.mem_filter]
  refine ⟨mem_states (k := k) (c := c) (t := i) ?_, by rw [heq, hcard2]⟩
  simp [times, Finset.mem_range]; omega

/-- The aligned doubles: those wide doubles whose chord is aligned. -/
def alignedDbl (k : ℕ) (c : ℕ → S) : Finset S :=
  (wideDbl k c).filter (fun s => dblHi k c s = 2 * k + 6 + dblLo k c s)

/-- The `PU`-doubles: those wide doubles whose tail endpoint is `u₁` or `u₂`
(Lemma 5.10(b), `lem:positions`). -/
def puDbl (k : ℕ) (c : ℕ → S) : Finset S :=
  (wideDbl k c).filter (fun s => 3 * k + 6 ≤ dblHi k c s)

/-- The `γ`-doubles: the non-aligned wide doubles whose prefix index lies to the left of
the aligned block (Lemma 5.10(a), `lem:positions`). -/
def gammaDbl (k : ℕ) (c : ℕ → S) (i1 : ℕ) : Finset S :=
  (wideDbl k c).filter (fun s => dblHi k c s ≤ 3 * k + 5 ∧
    dblHi k c s ≠ 2 * k + 6 + dblLo k c s ∧ dblLo k c s < i1)

/-- The `δ`-doubles: the non-aligned wide doubles whose prefix index lies to the right of
the aligned block (Lemma 5.10(a), `lem:positions`). -/
def deltaDbl (k : ℕ) (c : ℕ → S) (i2 : ℕ) : Finset S :=
  (wideDbl k c).filter (fun s => dblHi k c s ≤ 3 * k + 5 ∧
    dblHi k c s ≠ 2 * k + 6 + dblLo k c s ∧ i2 < dblLo k c s)

theorem alignedDbl_card_le : (alignedDbl k c).card ≤ (alignedSet k c).card := by
  classical
  refine Finset.card_le_card_of_injOn (fun s => dblLo k c s) ?_ ?_
  · intro s hs
    simp only [Finset.mem_coe, alignedDbl, Finset.mem_filter] at hs
    obtain ⟨hw, hal⟩ := hs
    obtain ⟨hlo, -, -, hclo, hchi⟩ := wideDbl_facts hw
    simp only [Finset.mem_coe, mem_alignedSet]
    exact ⟨hlo, by rw [hclo, ← hal, hchi]⟩
  · intro a ha b hb hab
    simp only [Finset.mem_coe, alignedDbl, Finset.mem_filter] at ha hb
    obtain ⟨-, -, -, hcloa, -⟩ := wideDbl_facts ha.1
    obtain ⟨-, -, -, hclob, -⟩ := wideDbl_facts hb.1
    rw [← hcloa, ← hclob]
    exact congrArg c hab

theorem puDbl_card_le : (puDbl k c).card ≤ 2 := by
  classical
  have : (puDbl k c).card ≤ (Finset.Icc (3 * k + 6) (3 * k + 7)).card := by
    refine Finset.card_le_card_of_injOn (fun s => dblHi k c s) ?_ ?_
    · intro s hs
      simp only [Finset.mem_coe, puDbl, Finset.mem_filter] at hs
      obtain ⟨-, -, hhin, -, -⟩ := wideDbl_facts hs.1
      simp only [Finset.mem_coe, Finset.mem_Icc]
      exact ⟨hs.2, hhin⟩
    · intro a ha b hb hab
      simp only [Finset.mem_coe, puDbl, Finset.mem_filter] at ha hb
      obtain ⟨-, -, -, -, hchia⟩ := wideDbl_facts ha.1
      obtain ⟨-, -, -, -, hchib⟩ := wideDbl_facts hb.1
      rw [← hchia, ← hchib]
      exact congrArg c hab
  simpa using this

/-- Three distinct non-run visits of one state are impossible (Lemma 4.5,
`lem:twovisit`, in the form `nvis_card_le_two`). -/
theorem no_three_nvis (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c) {s : S}
    {x y z : ℕ} (hx : x ∈ nvis k c s) (hy : y ∈ nvis k c s) (hz : z ∈ nvis k c s)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : False := by
  have hsub : ({x, y, z} : Finset ℕ) ⊆ nvis k c s := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with h | h | h <;> subst h <;> assumption
  have hc := Finset.card_le_card hsub
  rw [show ({x, y, z} : Finset ℕ).card = 3 by
    rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]), Finset.card_pair hyz]] at hc
  have := nvis_card_le_two hk huaw s
  omega

theorem dbl_nvis_nonempty {s : S} (hs : s ∈ twiceSet k c) : (nvis k c s).Nonempty := by
  simp only [twiceSet, Finset.mem_filter] at hs
  exact Finset.card_pos.1 (by omega)

/-- Neither index of a non-aligned wide chord `(j, 2k+6+j')` is an aligned index: a third
non-run visit of the state would contradict Lemma 4.5 (`lem:twovisit`).  This is the
remark preceding Lemma 5.10 (`lem:positions`). -/
theorem wide_nonaligned_notMem (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    {s : S} (hs : s ∈ wideDbl k c) (hhi : dblHi k c s ≤ 3 * k + 5)
    (hna : dblHi k c s ≠ 2 * k + 6 + dblLo k c s) :
    dblLo k c s ∉ alignedSet k c ∧ (dblHi k c s - (2 * k + 6)) ∉ alignedSet k c := by
  obtain ⟨hlo, hge, hle, hclo, hchi⟩ := wideDbl_facts hs
  have hne := dbl_nvis_nonempty (Finset.mem_filter.1 hs).1
  have hmlo := dblLo_mem hne
  have hmhi := dblHi_mem hne
  constructor
  · intro hmem
    rw [mem_alignedSet] at hmem
    have h3 : 2 * k + 6 + dblLo k c s ∈ nvis k c s := by
      rw [mem_nvis_iff]
      exact ⟨⟨by omega, by omega⟩, by rw [← hmem.2, hclo]⟩
    exact no_three_nvis hk huaw hmlo hmhi h3 (by omega) (by omega) (by omega)
  · intro hmem
    rw [mem_alignedSet] at hmem
    have h3 : dblHi k c s - (2 * k + 6) ∈ nvis k c s := by
      rw [mem_nvis_iff]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rw [hmem.2, show 2 * k + 6 + (dblHi k c s - (2 * k + 6)) = dblHi k c s by omega]
      exact hchi
    exact no_three_nvis hk huaw hmlo hmhi h3 (by omega) (by omega) (by omega)

/-- **Lemma 5.10(a),(b) (`lem:positions`)**, in the form used for the count: every wide
double is aligned, a `γ`-double, a `δ`-double or a `PU`-double. -/
theorem wideDbl_subset (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c) {i1 i2 : ℕ}
    (hI : ∀ t, i1 ≤ t → t ≤ i2 → t ∈ alignedSet k c) :
    wideDbl k c ⊆ alignedDbl k c ∪ gammaDbl k c i1 ∪ deltaDbl k c i2 ∪ puDbl k c := by
  intro s hs
  simp only [Finset.mem_union, alignedDbl, gammaDbl, deltaDbl, puDbl, Finset.mem_filter]
  by_cases hpu : 3 * k + 6 ≤ dblHi k c s
  · exact Or.inr ⟨hs, hpu⟩
  by_cases hal : dblHi k c s = 2 * k + 6 + dblLo k c s
  · exact Or.inl (Or.inl (Or.inl ⟨hs, hal⟩))
  · have hhi : dblHi k c s ≤ 3 * k + 5 := by omega
    obtain ⟨h1, -⟩ := wide_nonaligned_notMem hk huaw hs hhi hal
    have hout : dblLo k c s < i1 ∨ i2 < dblLo k c s := by
      by_contra hcon
      push_neg at hcon
      exact h1 (hI _ hcon.1 hcon.2)
    rcases hout with h | h
    · exact Or.inl (Or.inl (Or.inr ⟨hs, hhi, hal, h⟩))
    · exact Or.inl (Or.inr ⟨hs, hhi, hal, h⟩)

/-- **Lemma 5.10(a) (`lem:positions`)**: the tail-side index of a `γ`-chord lies to the
right of the aligned block. -/
theorem gamma_spread (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c) {i1 i2 : ℕ}
    (hi2 : i2 ∈ alignedSet k c) (hlb : ∀ t ∈ alignedSet k c, i1 ≤ t)
    {s : S} (hs : s ∈ gammaDbl k c i1) : i2 < dblHi k c s - (2 * k + 6) := by
  simp only [gammaDbl, Finset.mem_filter] at hs
  obtain ⟨hw, hhi, hna, hlo1⟩ := hs
  obtain ⟨hlo, hge, hle, hclo, hchi⟩ := wideDbl_facts hw
  obtain ⟨-, h2⟩ := wide_nonaligned_notMem hk huaw hw hhi hna
  rw [mem_alignedSet] at hi2
  have h12 : i1 ≤ i2 := hlb i2 (mem_alignedSet.2 hi2)
  have hj'ne : dblHi k c s - (2 * k + 6) ≠ i2 := by
    intro h; exact h2 (mem_alignedSet.2 (h ▸ hi2))
  by_contra hcon
  push_neg at hcon
  refine positions_wide_not_below hk huaw hi2.1 hi2.2 (j := dblLo k c s)
    (j' := dblHi k c s - (2 * k + 6)) (by omega) (by omega) (by omega) ?_
  rw [hclo, show 2 * k + 6 + (dblHi k c s - (2 * k + 6)) = dblHi k c s by omega, hchi]

/-- **Lemma 5.10(a) (`lem:positions`)**: the tail-side index of a `δ`-chord lies to the
left of the aligned block. -/
theorem delta_spread (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c) {i1 i2 : ℕ}
    (hi1 : i1 ∈ alignedSet k c) (hub : ∀ t ∈ alignedSet k c, t ≤ i2)
    {s : S} (hs : s ∈ deltaDbl k c i2) : dblHi k c s - (2 * k + 6) < i1 := by
  simp only [deltaDbl, Finset.mem_filter] at hs
  obtain ⟨hw, hhi, hna, hlo2⟩ := hs
  obtain ⟨hlo, hge, hle, hclo, hchi⟩ := wideDbl_facts hw
  obtain ⟨-, h2⟩ := wide_nonaligned_notMem hk huaw hw hhi hna
  rw [mem_alignedSet] at hi1
  have h12 : i1 ≤ i2 := hub i1 (mem_alignedSet.2 hi1)
  have hj'ne : dblHi k c s - (2 * k + 6) ≠ i1 := by
    intro h; exact h2 (mem_alignedSet.2 (h ▸ hi1))
  by_contra hcon
  push_neg at hcon
  refine positions_wide_not_above hk huaw hi1.2 (j := dblLo k c s)
    (j' := dblHi k c s - (2 * k + 6)) (by omega) (by omega) hlo (by omega) (by omega) ?_
  rw [hclo, show 2 * k + 6 + (dblHi k c s - (2 * k + 6)) = dblHi k c s by omega, hchi]

/-- **Lemma 5.12(a) (`lem:counts`)**: two `γ`-chords cannot have congruent shifts. -/
theorem gamma_pair (hk : 18 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) (htl : k - 1 ≤ Str.tt * Str.ell) {i1 i2 : ℕ}
    (hi2 : i2 ∈ alignedSet k c) (hlb : ∀ t ∈ alignedSet k c, i1 ≤ t)
    {a b : S} (ha : a ∈ gammaDbl k c i1) (hb : b ∈ gammaDbl k c i1)
    (hlt : dblLo k c a < dblLo k c b)
    (hcong : (dblHi k c a - (2 * k + 6) - dblLo k c a) % Str.ell
      = (dblHi k c b - (2 * k + 6) - dblLo k c b) % Str.ell) : False := by
  have hsa := gamma_spread (by omega) huaw hi2 hlb ha
  have hsb := gamma_spread (by omega) huaw hi2 hlb hb
  simp only [gammaDbl, Finset.mem_filter] at ha hb
  obtain ⟨hwa, hhia, hnaa, hlo1a⟩ := ha
  obtain ⟨hwb, hhib, hnab, hlo1b⟩ := hb
  obtain ⟨hloa, hgea, hlea, hcloa, hchia⟩ := wideDbl_facts hwa
  obtain ⟨hlob, hgeb, hleb, hclob, hchib⟩ := wideDbl_facts hwb
  have hi2k : i2 < k := (mem_alignedSet.1 hi2).1
  have h12 : i1 ≤ i2 := hlb i2 hi2
  have hea : c (dblLo k c a) = c (2 * k + 6 + (dblHi k c a - (2 * k + 6))) := by
    rw [hcloa, show 2 * k + 6 + (dblHi k c a - (2 * k + 6)) = dblHi k c a by omega, hchia]
  have heb : c (dblLo k c b) = c (2 * k + 6 + (dblHi k c b - (2 * k + 6))) := by
    rw [hclob, show 2 * k + 6 + (dblHi k c b - (2 * k + 6)) = dblHi k c b by omega, hchib]
  have hab : a ≠ b := by intro h; rw [h] at hlt; omega
  have hgt : dblHi k c b - (2 * k + 6) < dblHi k c a - (2 * k + 6) := by
    rcases Nat.lt_trichotomy (dblHi k c a - (2 * k + 6)) (dblHi k c b - (2 * k + 6))
      with h | h | h
    · obtain ⟨hfix, -⟩ := wide_chords_nested (by omega) huaw hlt hlob h (by omega) hea heb
      omega
    · exact absurd (by rw [← hchia, ← hchib]; congr 1; omega) hab
    · exact h
  have hmod : Nat.ModEq Str.ell (dblHi k c b - (2 * k + 6) - dblLo k c b)
      (dblHi k c a - (2 * k + 6) - dblLo k c a) := hcong.symm
  have hdvd : Str.ell ∣ ((dblHi k c a - (2 * k + 6)) - (dblHi k c b - (2 * k + 6))
      + (dblLo k c b - dblLo k c a)) := by
    have h := (Nat.modEq_iff_dvd' (by omega)).mp hmod
    rwa [show dblHi k c a - (2 * k + 6) - dblLo k c a
        - (dblHi k c b - (2 * k + 6) - dblLo k c b)
        = (dblHi k c a - (2 * k + 6)) - (dblHi k c b - (2 * k + 6))
          + (dblLo k c b - dblLo k c a) by omega] at h
  exact wide_chord_fold (by omega) huaw Str hlt hlob (by omega) hgt hea.symm heb hdvd
    (by omega)

/-- **Lemma 5.12(a) (`lem:counts`)**: two `δ`-chords cannot have congruent shifts. -/
theorem delta_pair (hk : 18 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) (htl : k - 1 ≤ Str.tt * Str.ell) {i1 i2 : ℕ}
    (hi1 : i1 ∈ alignedSet k c) (hub : ∀ t ∈ alignedSet k c, t ≤ i2)
    {a b : S} (ha : a ∈ deltaDbl k c i2) (hb : b ∈ deltaDbl k c i2)
    (hlt : dblLo k c a < dblLo k c b)
    (hcong : (dblLo k c a - (dblHi k c a - (2 * k + 6))) % Str.ell
      = (dblLo k c b - (dblHi k c b - (2 * k + 6))) % Str.ell) : False := by
  have hsa := delta_spread (by omega) huaw hi1 hub ha
  have hsb := delta_spread (by omega) huaw hi1 hub hb
  simp only [deltaDbl, Finset.mem_filter] at ha hb
  obtain ⟨hwa, hhia, hnaa, hlo2a⟩ := ha
  obtain ⟨hwb, hhib, hnab, hlo2b⟩ := hb
  obtain ⟨hloa, hgea, hlea, hcloa, hchia⟩ := wideDbl_facts hwa
  obtain ⟨hlob, hgeb, hleb, hclob, hchib⟩ := wideDbl_facts hwb
  have hi1k : i1 < k := (mem_alignedSet.1 hi1).1
  have h12 : i1 ≤ i2 := hub i1 hi1
  have hea : c (dblLo k c a) = c (2 * k + 6 + (dblHi k c a - (2 * k + 6))) := by
    rw [hcloa, show 2 * k + 6 + (dblHi k c a - (2 * k + 6)) = dblHi k c a by omega, hchia]
  have heb : c (dblLo k c b) = c (2 * k + 6 + (dblHi k c b - (2 * k + 6))) := by
    rw [hclob, show 2 * k + 6 + (dblHi k c b - (2 * k + 6)) = dblHi k c b by omega, hchib]
  have hab : a ≠ b := by intro h; rw [h] at hlt; omega
  have hgt : dblHi k c b - (2 * k + 6) < dblHi k c a - (2 * k + 6) := by
    rcases Nat.lt_trichotomy (dblHi k c a - (2 * k + 6)) (dblHi k c b - (2 * k + 6))
      with h | h | h
    · obtain ⟨hfix, -⟩ := wide_chords_nested (by omega) huaw hlt hlob h (by omega) hea heb
      omega
    · exact absurd (by rw [← hchia, ← hchib]; congr 1; omega) hab
    · exact h
  have hmod : Nat.ModEq Str.ell (dblLo k c a - (dblHi k c a - (2 * k + 6)))
      (dblLo k c b - (dblHi k c b - (2 * k + 6))) := hcong
  have hdvd : Str.ell ∣ ((dblHi k c a - (2 * k + 6)) - (dblHi k c b - (2 * k + 6))
      + (dblLo k c b - dblLo k c a)) := by
    have h := (Nat.modEq_iff_dvd' (by omega)).mp hmod
    rwa [show dblLo k c b - (dblHi k c b - (2 * k + 6))
        - (dblLo k c a - (dblHi k c a - (2 * k + 6)))
        = (dblHi k c a - (2 * k + 6)) - (dblHi k c b - (2 * k + 6))
          + (dblLo k c b - dblLo k c a) by omega] at h
  exact wide_chord_fold (by omega) huaw Str hlt hlob (by omega) hgt hea.symm heb hdvd
    (by omega)

/-- **Lemma 5.12(a) (`lem:counts`)**: there are at most `ℓ-1` `γ`-chords. -/
theorem gammaDbl_card_le (hk : 18 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) (htl : k - 1 ≤ Str.tt * Str.ell) {i1 i2 : ℕ}
    (hi1 : i1 ∈ alignedSet k c) (hi2 : i2 ∈ alignedSet k c)
    (hlb : ∀ t ∈ alignedSet k c, i1 ≤ t) :
    (gammaDbl k c i1).card ≤ Str.ell - 1 := by
  classical
  have hell := Str.hell
  have hmem : ∀ s ∈ gammaDbl k c i1,
      (dblHi k c s - (2 * k + 6) - dblLo k c s) % Str.ell ∈ Finset.Ico 1 Str.ell := by
    intro s hs
    have hsp := gamma_spread (by omega) huaw hi2 hlb hs
    simp only [gammaDbl, Finset.mem_filter] at hs
    obtain ⟨hlo, hge, hle, hclo, hchi⟩ := wideDbl_facts hs.1
    have hi1a := mem_alignedSet.1 hi1
    have h12 : i1 ≤ i2 := hlb i2 hi2
    rw [Finset.mem_Ico]
    refine ⟨?_, Nat.mod_lt _ (by omega)⟩
    by_contra hz
    have hdvd : Str.ell ∣ (dblHi k c s - (2 * k + 6) - dblLo k c s) :=
      Nat.dvd_of_mod_eq_zero (by omega)
    exact foldloop_lt (by omega) huaw Str (i := i1) (j := dblLo k c s)
      (j' := dblHi k c s - (2 * k + 6)) hs.2.2.2 (by omega) (by omega) hi1a.1 hi1a.2
      (by rw [hclo, show 2 * k + 6 + (dblHi k c s - (2 * k + 6)) = dblHi k c s by omega,
        hchi]) hdvd (by omega)
  have hinj : ∀ a ∈ gammaDbl k c i1, ∀ b ∈ gammaDbl k c i1,
      (dblHi k c a - (2 * k + 6) - dblLo k c a) % Str.ell
        = (dblHi k c b - (2 * k + 6) - dblLo k c b) % Str.ell → a = b := by
    intro a ha b hb hcong
    by_contra hab
    have hlone : dblLo k c a ≠ dblLo k c b := by
      intro h
      simp only [gammaDbl, Finset.mem_filter] at ha hb
      obtain ⟨-, -, -, hcloa, -⟩ := wideDbl_facts ha.1
      obtain ⟨-, -, -, hclob, -⟩ := wideDbl_facts hb.1
      exact hab (by rw [← hcloa, ← hclob, h])
    rcases lt_or_gt_of_ne hlone with h | h
    · exact gamma_pair hk huaw Str htl hi2 hlb ha hb h hcong
    · exact gamma_pair hk huaw Str htl hi2 hlb hb ha h hcong.symm
  have hcard := Finset.card_le_card_of_injOn
    (f := fun s => (dblHi k c s - (2 * k + 6) - dblLo k c s) % Str.ell)
    (s := gammaDbl k c i1) (t := Finset.Ico 1 Str.ell)
    (fun s hs => hmem s hs) (fun a ha b hb h => hinj a ha b hb h)
  simpa using hcard

/-- **Lemma 5.12(a) (`lem:counts`)**: there are at most `ℓ-1` `δ`-chords. -/
theorem deltaDbl_card_le (hk : 18 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) (htl : k - 1 ≤ Str.tt * Str.ell) {i1 i2 : ℕ}
    (hi1 : i1 ∈ alignedSet k c) (hub : ∀ t ∈ alignedSet k c, t ≤ i2) :
    (deltaDbl k c i2).card ≤ Str.ell - 1 := by
  classical
  have hell := Str.hell
  have hmem : ∀ s ∈ deltaDbl k c i2,
      (dblLo k c s - (dblHi k c s - (2 * k + 6))) % Str.ell ∈ Finset.Ico 1 Str.ell := by
    intro s hs
    have hsp := delta_spread (by omega) huaw hi1 hub hs
    simp only [deltaDbl, Finset.mem_filter] at hs
    obtain ⟨hlo, hge, hle, hclo, hchi⟩ := wideDbl_facts hs.1
    have hi1a := mem_alignedSet.1 hi1
    have h12 : i1 ≤ i2 := hub i1 hi1
    rw [Finset.mem_Ico]
    refine ⟨?_, Nat.mod_lt _ (by omega)⟩
    by_contra hz
    have hdvd : Str.ell ∣ (dblLo k c s - (dblHi k c s - (2 * k + 6))) :=
      Nat.dvd_of_mod_eq_zero (by omega)
    exact foldloop_gt (by omega) huaw Str (i := i1) (j := dblLo k c s)
      (j' := dblHi k c s - (2 * k + 6)) hsp (by omega) hlo hi1a.2
      (by rw [hclo, show 2 * k + 6 + (dblHi k c s - (2 * k + 6)) = dblHi k c s by omega,
        hchi]) hdvd (by omega)
  have hinj : ∀ a ∈ deltaDbl k c i2, ∀ b ∈ deltaDbl k c i2,
      (dblLo k c a - (dblHi k c a - (2 * k + 6))) % Str.ell
        = (dblLo k c b - (dblHi k c b - (2 * k + 6))) % Str.ell → a = b := by
    intro a ha b hb hcong
    by_contra hab
    have hlone : dblLo k c a ≠ dblLo k c b := by
      intro h
      simp only [deltaDbl, Finset.mem_filter] at ha hb
      obtain ⟨-, -, -, hcloa, -⟩ := wideDbl_facts ha.1
      obtain ⟨-, -, -, hclob, -⟩ := wideDbl_facts hb.1
      exact hab (by rw [← hcloa, ← hclob, h])
    rcases lt_or_gt_of_ne hlone with h | h
    · exact delta_pair hk huaw Str htl hi1 hub ha hb h hcong
    · exact delta_pair hk huaw Str htl hi1 hub hb ha h hcong.symm
  have hcard := Finset.card_le_card_of_injOn
    (f := fun s => (dblLo k c s - (dblHi k c s - (2 * k + 6))) % Str.ell)
    (s := deltaDbl k c i2) (t := Finset.Ico 1 Str.ell)
    (fun s hs => hmem s hs) (fun a ha b hb h => hinj a ha b hb h)
  simpa using hcard

/-- **Lemma 4.6 (Aligned block, `lem:block`)**: the set `I` of aligned indices is the
interval `[i₁,i₂]` between its smallest and its largest element. -/
theorem alignedSet_interval (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (hAne : (alignedSet k c).Nonempty) :
    ∀ t, (alignedSet k c).min' hAne ≤ t → t ≤ (alignedSet k c).max' hAne →
      t ∈ alignedSet k c := by
  have hi1 : (alignedSet k c).min' hAne ∈ alignedSet k c := Finset.min'_mem _ _
  have hi2 : (alignedSet k c).max' hAne ∈ alignedSet k c := Finset.max'_mem _ _
  have hi1a := mem_alignedSet.1 hi1
  have hi2a := mem_alignedSet.1 hi2
  have hle : (alignedSet k c).min' hAne ≤ (alignedSet k c).max' hAne :=
    Finset.min'_le _ _ hi2
  intro t h1 h2
  rcases Nat.eq_or_lt_of_le hle with heq | hlt
  · have hte : t = (alignedSet k c).min' hAne := by omega
    rw [hte]; exact hi1
  · have hbl := aligned_block hk huaw
      (i := (alignedSet k c).min' hAne) (p := (alignedSet k c).max' hAne) hlt (by omega)
      (by rw [show (alignedSet k c).min' hAne + (2 * k + 6)
            = 2 * k + 6 + (alignedSet k c).min' hAne by omega]; exact hi1a.2)
      (by rw [show (alignedSet k c).max' hAne + (2 * k + 6)
            = 2 * k + 6 + (alignedSet k c).max' hAne by omega]; exact hi2a.2)
    refine mem_alignedSet.2 ⟨by omega, ?_⟩
    have := hbl t h1 h2
    rwa [show t + (2 * k + 6) = 2 * k + 6 + t by omega] at this

/-- `|I| ≤ i₂ + 1`: the aligned block lies in `[0, i₂]`. -/
theorem alignedSet_card_le_max (hAne : (alignedSet k c).Nonempty) :
    (alignedSet k c).card ≤ (alignedSet k c).max' hAne + 1 := by
  have : alignedSet k c ⊆ Finset.range ((alignedSet k c).max' hAne + 1) := by
    intro t ht
    exact Finset.mem_range.2 (by have := Finset.le_max' _ t ht; omega)
  simpa using Finset.card_le_card this

/-- `|I| + i₁ ≤ k`: the aligned block lies in `[i₁, k-1]`. -/
theorem alignedSet_card_add_min_le (hAne : (alignedSet k c).Nonempty) :
    (alignedSet k c).card + (alignedSet k c).min' hAne ≤ k := by
  have hsub : alignedSet k c ⊆ Finset.Ico ((alignedSet k c).min' hAne) k := by
    intro t ht
    exact Finset.mem_Ico.2 ⟨Finset.min'_le _ t ht, (mem_alignedSet.1 ht).1⟩
  have := Finset.card_le_card hsub
  rw [Nat.card_Ico] at this
  have hmk : (alignedSet k c).min' hAne < k := (mem_alignedSet.1 (Finset.min'_mem _ hAne)).1
  omega

/-- **Lemma 5.12(c) (`lem:counts`)**: the number `b^# = k - |I|` of broken indices
satisfies `2 b^# + 2 ≤ 2(3ℓ-1) + b₁ + s₀`, i.e. `b^# ≤ 3ℓ - 2 + (b₁+s₀)/2`. -/
theorem blockCount_bound (hk : 18 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) (hd0le : Str.d0 + Str.ell ≤ 7)
    {i0 : ℕ} (hi0 : i0 < k) (halign0 : c i0 = c (2 * k + 6 + i0)) :
    2 * k + 2 ≤ 2 * ((alignedSet k c).card + (3 * Str.ell - 1))
      + bridgeCount k c + singleCount k c := by
  classical
  have hell := Str.hell
  have hadd := Str.d0_add
  have htl : k - 1 ≤ Str.tt * Str.ell := by omega
  have hAne : (alignedSet k c).Nonempty := ⟨i0, mem_alignedSet.2 ⟨hi0, halign0⟩⟩
  have hi1 : (alignedSet k c).min' hAne ∈ alignedSet k c := Finset.min'_mem _ _
  have hi2 : (alignedSet k c).max' hAne ∈ alignedSet k c := Finset.max'_mem _ _
  have hlb : ∀ t ∈ alignedSet k c, (alignedSet k c).min' hAne ≤ t :=
    fun t ht => Finset.min'_le _ _ ht
  have hub : ∀ t ∈ alignedSet k c, t ≤ (alignedSet k c).max' hAne :=
    fun t ht => Finset.le_max' _ _ ht
  have hI := alignedSet_interval (by omega : 3 ≤ k) huaw hAne
  have hsub : twiceSet k c ⊆ narrowDbl k c ∪
      (alignedDbl k c ∪ gammaDbl k c ((alignedSet k c).min' hAne)
        ∪ deltaDbl k c ((alignedSet k c).max' hAne) ∪ puDbl k c) := by
    intro s hs
    rcases Finset.mem_union.1 (twiceSet_subset_union hs) with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (wideDbl_subset (by omega) huaw hI h)
  have hn := narrowDbl_card_le hk huaw Str hd0le
  have hg := gammaDbl_card_le hk huaw Str htl hi1 hi2 hlb
  have hd := deltaDbl_card_le hk huaw Str htl hi1 hub
  have ha := alignedDbl_card_le (k := k) (c := c)
  have hp := puDbl_card_le (k := k) (c := c)
  have hcard : (twiceSet k c).card ≤ (alignedSet k c).card + (3 * Str.ell - 1) := by
    refine le_trans (Finset.card_le_card hsub) ?_
    refine le_trans (Finset.card_union_le _ _) ?_
    have h1 := Finset.card_union_le
      (alignedDbl k c ∪ gammaDbl k c ((alignedSet k c).min' hAne)
        ∪ deltaDbl k c ((alignedSet k c).max' hAne)) (puDbl k c)
    have h2 := Finset.card_union_le
      (alignedDbl k c ∪ gammaDbl k c ((alignedSet k c).min' hAne))
      (deltaDbl k c ((alignedSet k c).max' hAne))
    have h3 := Finset.card_union_le (alignedDbl k c)
      (gammaDbl k c ((alignedSet k c).min' hAne))
    omega
  have hcn := count_nonrun (by omega : 3 ≤ k) huaw
  have hco := card_onceSet (by omega : 3 ≤ k) huaw
  omega

end

end AneVsAn
