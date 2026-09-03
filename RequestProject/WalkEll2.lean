import RequestProject.WalkLooseCount
import RequestProject.WalkSurgery2

/-!
# The clean shape `ℓ = 2` (Proposition 6.7, `prop:ell2clean`)

This file formalizes Lemma 6.6(c),(d) (`lem:parity2`) and Proposition 6.7
(`prop:ell2clean`) of `ane-vs-an-separation-v4_1.tex`.

The clean shape is `ℓ = 2`, `d₀ = 3`, `x₁ = 2`, `b₁ = s₀ = 0`.  The argument runs as
follows.

* `no_two_pu` is Lemma 6.6(c) (`lem:parity2`): there is at most one `PU`-chord.  Indeed
  a `PU`-chord `g_j = u₁` with `k-j` even is killed by the lasso of Lemma 5.9
  (`lem:lasso`), and one with `k+1-j` even likewise; two `PU`-chords of odd `λ` are
  killed by Lemma 5.7(i) (`lem:wide`) when `j₁ < j₂` and by the `e`-edge path
  `pu_swap` when `j₂ < j₁`.
* Hence (Lemma 6.6(d), `lem:parity2`) `u₁` does not lie in a `PU`-chord, so its partner
  is a tail state: `u₁` lies in the unique narrow chord, a `TU`-chord.
* The four tallies of `RequestProject/WalkLooseCount.lean` then give `β = r = 1`,
  `γ = 0`, `δ = 1`, hence `J_R = {k-1}` and the `TU`-chord is `(3k+5, 3k+6)`, of
  length `1`, which Lemma 5.6(b) (`lem:narrow`) with `σ = 2` excludes.
-/

namespace AneVsAn

set_option autoImplicit false

section

variable {k : ℕ} {S : Type} [DecidableEq S] {c : ℕ → S}

theorem mem_nonRunTimes_of {t : ℕ} (h1 : t < 3 * k + 8) (h2 : ¬ (k ≤ t ∧ t ≤ 2 * k + 5)) :
    t ∈ nonRunTimes k := by
  simp only [nonRunTimes, times, runTimes, Finset.mem_sdiff, Finset.mem_range, Finset.mem_Icc]
  exact ⟨h1, h2⟩

/-- **Lemma 6.6(c) (`lem:parity2`)**, for `ℓ = 2`: there is at most one `PU`-chord.  If
`g_{j₁} = u₁` and `g_{j₂} = u₂` are two `PU`-chords then, unless one of the lassos of
Lemma 5.9 (`lem:lasso`) applies, both `k-j₁` and `k+1-j₂` are odd; then `j₁ < j₂` is
excluded by Lemma 5.7(i) (`lem:wide`) and `j₂ < j₁` by the `e`-edge path `pu_swap`. -/
theorem no_two_pu (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) (hell : Str.ell = 2) (htl : k + 1 ≤ Str.tt * Str.ell)
    {i j₁ j₂ : ℕ} (hik : i < k) (halign : c i = c (2 * k + 6 + i))
    (hj1 : j₁ < k) (hj2 : j₂ < k) (hne : j₁ ≠ j₂)
    (h1 : c j₁ = c (3 * k + 6)) (h2 : c j₂ = c (3 * k + 7)) : False := by
  -- both prefix indices lie strictly below the aligned index `i`
  have hlt1 : j₁ < i := by
    rcases Nat.lt_trichotomy j₁ i with h | h | h
    · exact h
    · exfalso
      refine no_three_nvis hk huaw (s := c i) (x := i) (y := 2 * k + 6 + i) (z := 3 * k + 6)
        (mem_nvis_iff.2 ⟨⟨by omega, by omega⟩, rfl⟩)
        (mem_nvis_iff.2 ⟨⟨by omega, by omega⟩, halign.symm⟩)
        (mem_nvis_iff.2 ⟨⟨by omega, by omega⟩, by rw [← h1, h]⟩)
        (by omega) (by omega) (by omega)
    · exact absurd (positions_PU hk huaw halign h hj1 (Or.inl rfl) h1) (fun h => h.elim)
  have hlt2 : j₂ < i := by
    rcases Nat.lt_trichotomy j₂ i with h | h | h
    · exact h
    · exfalso
      refine no_three_nvis hk huaw (s := c i) (x := i) (y := 2 * k + 6 + i) (z := 3 * k + 7)
        (mem_nvis_iff.2 ⟨⟨by omega, by omega⟩, rfl⟩)
        (mem_nvis_iff.2 ⟨⟨by omega, by omega⟩, halign.symm⟩)
        (mem_nvis_iff.2 ⟨⟨by omega, by omega⟩, by rw [← h2, h]⟩)
        (by omega) (by omega) (by omega)
    · exact absurd (positions_PU hk huaw halign h hj2 (Or.inr rfl) h2) (fun h => h.elim)
  by_cases hp1 : (k - j₁) % 2 = 0
  · exact lasso_u1 hk huaw Str hlt1 hik halign h1 (by rw [hell]; omega) (by omega)
  by_cases hp2 : (k + 1 - j₂) % 2 = 0
  · exact lasso_u2 hk huaw Str hlt2 hik halign h2 (by rw [hell]; omega) (by omega)
  rcases lt_or_gt_of_ne hne with h | h
  · -- `j₁ < j₂`: the two wide chords `(j₁,k)` and `(j₂,k+1)` have increasing indices
    obtain ⟨ha, -⟩ := wide_chords_nested hk huaw (ja := j₁) (jb := j₂) (ja' := k)
      (jb' := k + 1) h hj2 (by omega) (by omega)
      (by rw [h1]; congr 1; omega) (by rw [h2]; congr 1; omega)
    omega
  · -- `j₂ < j₁`: the `e`-edge path
    exact pu_swap hk huaw Str h hj1 h1 h2 (by rw [hell]; omega) (by omega)

/-- **Proposition 6.7 (`prop:ell2clean`)**: the clean shape `ℓ = 2`, `d₀ = 3`,
`b₁ = s₀ = 0` is impossible. -/
theorem ell2_clean (hk : 18 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) (hell : Str.ell = 2) (hd : Str.d0 = 3)
    (hb : bridgeCount k c = 0) (hs0 : singleCount k c = 0)
    {i0 : ℕ} (hi0 : i0 < k) (halign0 : c i0 = c (2 * k + 6 + i0)) : False := by
  classical
  have hk3 : (3 : ℕ) ≤ k := by omega
  have hadd := Str.d0_add
  have htl : Str.tt * Str.ell = k + 2 := by omega
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
  -- the two `u`-states are doubles
  have hs1 : c (3 * k + 6) ∈ twiceSet k c :=
    nonrun_double hk3 huaw hb hs0 (mem_nonRunTimes_of (by omega) (by omega))
  have hs2 : c (3 * k + 7) ∈ twiceSet k c :=
    nonrun_double hk3 huaw hb hs0 (mem_nonRunTimes_of (by omega) (by omega))
  have hs1nv : 3 * k + 6 ∈ nvis k c (c (3 * k + 6)) :=
    mem_nvis_iff.2 ⟨⟨by omega, by omega⟩, rfl⟩
  have hs2nv : 3 * k + 7 ∈ nvis k c (c (3 * k + 7)) :=
    mem_nvis_iff.2 ⟨⟨by omega, by omega⟩, rfl⟩
  obtain ⟨hlt1, hlo1s, hhi1s, hhi1n, hclo1, hchi1⟩ := dbl_chord hs1
  obtain ⟨hlt2, hlo2s, hhi2s, hhi2n, hclo2, hchi2⟩ := dbl_chord hs2
  have hlo1le : dblLo k c (c (3 * k + 6)) ≤ 3 * k + 6 := dblLo_le hs1nv
  have hhi1ge : 3 * k + 6 ≤ dblHi k c (c (3 * k + 6)) := le_dblHi hs1nv
  have hhi2ge : 3 * k + 7 ≤ dblHi k c (c (3 * k + 7)) := le_dblHi hs2nv
  have hHi2 : dblHi k c (c (3 * k + 7)) = 3 * k + 7 := by omega
  have hne12 : c (3 * k + 6) ≠ c (3 * k + 7) := fun h => positions_u1_ne_u2 hk3 huaw Str h
  have hHi1 : dblHi k c (c (3 * k + 6)) = 3 * k + 6 := by
    by_contra hcon
    have h7 : dblHi k c (c (3 * k + 6)) = 3 * k + 7 := by omega
    exact hne12 (by rw [← h7]; exact hchi1.symm)
  -- `u₁` does not lie in a `PU`-chord (Lemma 6.6(d), `lem:parity2`)
  have hLo1tail : 2 * k + 6 ≤ dblLo k c (c (3 * k + 6)) := by
    rcases hlo1s with hj1 | h
    · exfalso
      -- `g_{j₁} = u₁`; look at the partner of `u₂`
      have hu1 : c (dblLo k c (c (3 * k + 6))) = c (3 * k + 6) := hclo1
      rcases hlo2s with hj2 | hj2
      · exact no_two_pu hk3 huaw Str hell (by omega) hi1k hi1al hj1 hj2
          (fun h => hne12 (by rw [← hclo1, h, hclo2])) hu1 hclo2
      · rcases (by omega : dblLo k c (c (3 * k + 7)) = 3 * k + 6 ∨
          dblLo k c (c (3 * k + 7)) < 3 * k + 6) with h36 | h36
        · exact hne12 (by rw [← h36]; exact hclo2)
        · refine positions_PU_TU_incompatible hk3 huaw (j := dblLo k c (c (3 * k + 6)))
            (j' := dblLo k c (c (3 * k + 7)) - (2 * k + 6)) hj1 (by omega) hu1 ?_
          rw [show 2 * k + 6 + (dblLo k c (c (3 * k + 7)) - (2 * k + 6))
            = dblLo k c (c (3 * k + 7)) by omega]
          exact hclo2
    · exact h
  -- so `u₁` is the (unique) narrow chord
  have hs1n : c (3 * k + 6) ∈ narrowDbl k c :=
    Finset.mem_filter.2 ⟨hs1, Or.inr hLo1tail⟩
  have hncard := narrowDbl_card_le hk huaw Str (by omega)
  have hnarrow : narrowDbl k c = {c (3 * k + 6)} := by
    have h1 : 1 ≤ (narrowDbl k c).card := Finset.card_pos.2 ⟨_, hs1n⟩
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 (by omega : (narrowDbl k c).card = 1)
    rw [ha] at hs1n ⊢
    rw [Finset.mem_singleton.1 hs1n]
  -- the tail index of the `TU`-chord lies in `J_R`
  have hj'k : dblLo k c (c (3 * k + 6)) - (2 * k + 6) < k := by omega
  have hj'chord : c (2 * k + 6 + (dblLo k c (c (3 * k + 6)) - (2 * k + 6))) = c (3 * k + 6) := by
    rw [show 2 * k + 6 + (dblLo k c (c (3 * k + 6)) - (2 * k + 6))
      = dblLo k c (c (3 * k + 6)) by omega]
    exact hclo1
  have hj'2 : i2 < dblLo k c (c (3 * k + 6)) - (2 * k + 6) := by
    rcases Nat.lt_trichotomy (dblLo k c (c (3 * k + 6)) - (2 * k + 6)) i2 with h | h | h
    · exact absurd (positions_TU hk3 huaw hi2k hi2al h (Or.inl rfl) hj'chord) (fun h => h.elim)
    · exfalso
      refine no_three_nvis hk3 huaw (s := c (3 * k + 6)) (x := i2)
        (y := dblLo k c (c (3 * k + 6))) (z := 3 * k + 6)
        (mem_nvis_iff.2 ⟨⟨by omega, by omega⟩, by rw [hi2al, ← h]; exact hj'chord⟩)
        (dblLo_mem ⟨_, hs1nv⟩) hs1nv (by omega) (by omega) (by omega)
    · exact h
  -- `u₂` lies in the unique `PU`-chord
  have hs2pu : c (3 * k + 7) ∈ puDbl k c := by
    have hlo2k : dblLo k c (c (3 * k + 7)) < k := by
      rcases hlo2s with h | h
      · exact h
      · exfalso
        have : c (3 * k + 7) ∈ narrowDbl k c := Finset.mem_filter.2 ⟨hs2, Or.inr h⟩
        rw [hnarrow, Finset.mem_singleton] at this
        exact hne12 this.symm
    exact Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hs2, hlo2k, by omega⟩, by omega⟩
  have hpu : puDbl k c = {c (3 * k + 7)} := by
    refine Finset.eq_singleton_iff_unique_mem.2 ⟨hs2pu, ?_⟩
    intro s hs
    obtain ⟨-, hge, hle⟩ := puDbl_pos hk3 huaw hi1 hs
    obtain ⟨-, -, -, -, hchi⟩ := wideDbl_facts (puDbl_subset_wide hs)
    rcases (by omega : dblHi k c s = 3 * k + 6 ∨ dblHi k c s = 3 * k + 7) with h | h
    · exfalso
      rw [h] at hchi
      have : s ∈ narrowDbl k c := by rw [hnarrow, Finset.mem_singleton, ← hchi]
      exact Finset.disjoint_left.1 disj_narrow_wide this (puDbl_subset_wide hs)
    · rw [h] at hchi; exact hchi.symm
  -- the four tallies
  have hT1 := count_prefix_left hk3 huaw hb hs0 hi1 hi2 hlb hI
  have hT2 := count_prefix_right hk3 huaw hb hs0 hi1 hi2 hlb hub hI
  have hT3 := count_tail_left hk3 huaw hb hs0 hi1 hi2 hlb hI
  have hT4 := count_tail_right hk3 huaw hb hs0 hi1 hi2 hlb hub hI
  rw [hnarrow] at hT1 hT2 hT3 hT4
  rw [Finset.filter_singleton, if_neg (by omega), Finset.filter_singleton,
    if_neg (by omega)] at hT1
  rw [Finset.filter_singleton, if_neg (by omega), Finset.filter_singleton,
    if_neg (by omega)] at hT2
  rw [Finset.filter_singleton, if_neg (by omega), Finset.filter_singleton,
    if_neg (by omega)] at hT3
  rw [Finset.filter_singleton, if_pos (by omega), Finset.filter_singleton,
    if_neg (by omega)] at hT4
  rw [hpu] at hT1
  simp only [Finset.card_empty, Finset.card_singleton] at hT1 hT2 hT3 hT4
  have hg := gammaDbl_card_le hk huaw Str (by omega) hi1 hi2 hlb
  have hdd := deltaDbl_card_le hk huaw Str (by omega) hi1 hub
  rw [hell] at hg hdd
  -- `β = r = 1`, `γ = 0`, `δ = 1`, so `J_R = {k-1}` and the `TU`-chord has length one
  have hi2v : i2 = k - 2 := by omega
  have hlov : dblLo k c (c (3 * k + 6)) = 3 * k + 5 := by omega
  refine narrow_tail_insert hk3 huaw Str (i := 3 * k + 5) (j := 3 * k + 6) (σ := 2)
    (by omega) (by omega) (by omega) ?_ (by omega) ?_ ?_
  · rw [← hlov]; exact hclo1
  · rw [hell, show 3 * k + 6 - (3 * k + 5) = 1 by omega]
  · rw [show 3 * k + 6 - (3 * k + 5) = 1 by omega]; omega

end

end AneVsAn
