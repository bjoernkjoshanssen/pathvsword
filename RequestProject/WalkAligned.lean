import RequestProject.WalkBridges

/-!
# The aligned block is nonempty (Lemma 5.11, `lem:Inonempty`)

This file formalizes Lemma 5.11 (`lem:Inonempty`) of `ane-vs-an-separation-v4_1.tex`
together with the case (c) of Lemma 5.6 (Narrow surgeries, `lem:narrow`) that its proof
needs.

The argument of the source counts the doubles `f`:

* the narrow chords have pairwise distinct lengths modulo `ℓ`, and no length divisible by
  `ℓ`, so there are at most `ℓ-1` of them;
* the wide chords have strictly decreasing shifts, and two wide chords whose shifts are
  congruent modulo `ℓ` have shifts at distance at least `k`, so there are at most `3` of
  them in each residue class, i.e. at most `3ℓ` in all;

whence `f ≤ 4ℓ-1` and `2k+2 = 2f+b₁+s₀ ≤ 6ℓ+6 ≤ 30`, contradicting `k ≥ 18`.
-/

namespace AneVsAn

set_option autoImplicit false

section

variable {k : ℕ} {S : Type} {c : ℕ → S}

/-- **Lemma 5.6(c) (Narrow surgeries, `lem:narrow`)**: two distinct narrow chords
`(i₁,j₁)` and `(i₂,j₂)` (listed so that `i₁ < i₂`) cannot have lengths congruent modulo
`ℓ`.

The proof is the one of the source: the two lengths are distinct (Corollary 4.4,
`cor:shifts`, in the form `narrow_lengths_distinct`), and the path that inserts the first
chord and skips the second one — `narrow_prefix_pair`, `narrow_tail_pair` or
`narrow_mixed_pair` according to the sides on which the two chords lie — has length `n`
once the run is replaced by `R⟨m-λ₁+λ₂⟩`, which is available because
`λ₁-λ₂ ≤ k ≤ tℓ`. -/
theorem narrow_pair_mod (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) (htl : k ≤ Str.tt * Str.ell)
    {i₁ j₁ i₂ j₂ : ℕ} (h1 : i₁ < j₁) (h2 : i₂ < j₂) (h12 : i₁ < i₂)
    (hn1 : j₁ < k ∨ (2 * k + 6 ≤ i₁ ∧ j₁ ≤ 3 * k + 7))
    (hn2 : j₂ < k ∨ (2 * k + 6 ≤ i₂ ∧ j₂ ≤ 3 * k + 7))
    (e1 : c i₁ = c j₁) (e2 : c i₂ = c j₂)
    (hmod : (j₁ - i₁) % Str.ell = (j₂ - i₂) % Str.ell) : False := by
  have hd0 := Str.d0_add
  have hell := Str.hell
  -- the two lengths are distinct (Corollary 4.4, `cor:shifts`)
  have hlne : j₁ - i₁ ≠ j₂ - i₂ := by
    intro h
    refine narrow_lengths_distinct hk huaw (i := i₁) (p := i₂) (lam := j₁ - i₁) h12
      (by omega) ?_ ?_ ?_ ?_
    · rcases hn1 with h' | h'
      exacts [Or.inl (by omega), Or.inr ⟨by omega, by omega⟩]
    · rcases hn2 with h' | h'
      exacts [Or.inl (by omega), Or.inr ⟨by omega, by omega⟩]
    · rw [show i₁ + (j₁ - i₁) = j₁ by omega]; exact e1
    · rw [show i₂ + (j₁ - i₁) = j₂ by omega]; exact e2
  -- the new run length `m - λ₁ + λ₂` is available
  have hlam1 : j₁ - i₁ ≤ k + 1 := by rcases hn1 with h' | h' <;> omega
  have hle : j₁ - i₁ ≤ Str.tt * Str.ell + (j₂ - i₂) := by omega
  have hcong : (j₁ - i₁) % Str.ell = (Str.tt * Str.ell + (j₂ - i₂)) % Str.ell := by
    rw [Nat.mul_comm, Nat.mul_add_mod]
    exact hmod
  obtain ⟨u, hu⟩ := (Nat.modEq_iff_dvd' hle).mp hcong
  have hu' : u * Str.ell = Str.tt * Str.ell + (j₂ - i₂) - (j₁ - i₁) := by
    rw [Nat.mul_comm]; exact hu.symm
  have key : Str.d0 + u * Str.ell + (j₁ - i₁) = k + 5 + (j₂ - i₂) := by omega
  -- three configurations, according to the sides of the two chords
  rcases hn1 with hp1 | ht1
  · rcases hn2 with hp2 | ht2
    · -- both chords on the prefix side
      exact narrow_prefix_pair hk huaw Str (a₁ := i₁) (a₂ := j₁) (x := i₂) (y := j₂)
        (u := u) h12 h1 hp1 (by omega) (by omega) e1 e2 (by omega)
    · -- the first chord on the prefix side, the second on the tail side
      exact narrow_mixed_pair hk huaw Str (a₁ := i₁) (a₂ := j₁) (x := i₂) (y := j₂)
        (u := u) h1 hp1 ht2.1 (by omega) (by omega) e1 e2 (by omega)
  · -- both chords on the tail side
    have ht2 : 2 * k + 6 ≤ i₂ ∧ j₂ ≤ 3 * k + 7 := by
      rcases hn2 with h' | h'
      · omega
      · exact h'
    exact narrow_tail_pair hk huaw Str (a₁ := i₁) (a₂ := j₁) (x := i₂) (y := j₂)
      (u := u) ht1.1 h1 ht1.2 (by omega) (by omega) (by omega) e1 e2 (by omega) (by omega)

end

section

variable {k : ℕ} {S : Type} [DecidableEq S] {c : ℕ → S}

/-- The earlier of the two non-run visits of a *double* (Section 5.1, `sec:budget`): the
left endpoint of its chord. -/
def dblLo (k : ℕ) (c : ℕ → S) (s : S) : ℕ :=
  if h : (nvis k c s).Nonempty then (nvis k c s).min' h else 0

/-- The later of the two non-run visits of a *double* (Section 5.1, `sec:budget`): the
right endpoint of its chord. -/
def dblHi (k : ℕ) (c : ℕ → S) (s : S) : ℕ :=
  if h : (nvis k c s).Nonempty then (nvis k c s).max' h else 0

theorem dblLo_eq {s : S} (hne : (nvis k c s).Nonempty) :
    dblLo k c s = (nvis k c s).min' hne := by simp [dblLo, hne]

theorem dblHi_eq {s : S} (hne : (nvis k c s).Nonempty) :
    dblHi k c s = (nvis k c s).max' hne := by simp [dblHi, hne]

theorem dblLo_mem {s : S} (hne : (nvis k c s).Nonempty) : dblLo k c s ∈ nvis k c s := by
  rw [dblLo_eq hne]; exact Finset.min'_mem _ _

theorem dblHi_mem {s : S} (hne : (nvis k c s).Nonempty) : dblHi k c s ∈ nvis k c s := by
  rw [dblHi_eq hne]; exact Finset.max'_mem _ _

theorem dblLo_le {s : S} {t : ℕ} (ht : t ∈ nvis k c s) : dblLo k c s ≤ t := by
  rw [dblLo_eq ⟨t, ht⟩]; exact Finset.min'_le _ _ ht

theorem le_dblHi {s : S} {t : ℕ} (ht : t ∈ nvis k c s) : t ≤ dblHi k c s := by
  rw [dblHi_eq ⟨t, ht⟩]; exact Finset.le_max' _ _ ht

theorem mem_nvis_iff {s : S} {t : ℕ} :
    t ∈ nvis k c s ↔ (t < 3 * k + 8 ∧ ¬ (k ≤ t ∧ t ≤ 2 * k + 5)) ∧ c t = s := by
  simp [nvis, nonRunTimes, times, runTimes, Finset.mem_filter, Finset.mem_sdiff,
    Finset.mem_range, Finset.mem_Icc, and_assoc]

/-- The two endpoints of the chord of a double, with their basic properties: they are
non-run times carrying the state, and the left one precedes the right one. -/
theorem dbl_chord {s : S} (hs : s ∈ twiceSet k c) :
    dblLo k c s < dblHi k c s ∧
      (dblLo k c s < k ∨ 2 * k + 6 ≤ dblLo k c s) ∧
      (dblHi k c s < k ∨ 2 * k + 6 ≤ dblHi k c s) ∧
      dblHi k c s ≤ 3 * k + 7 ∧ c (dblLo k c s) = s ∧ c (dblHi k c s) = s := by
  simp only [twiceSet, Finset.mem_filter] at hs
  have hne : (nvis k c s).Nonempty := Finset.card_pos.1 (by omega)
  have hlo : dblLo k c s = (nvis k c s).min' hne := by simp [dblLo, hne]
  have hhi : dblHi k c s = (nvis k c s).max' hne := by simp [dblHi, hne]
  have hlomem := (nvis k c s).min'_mem hne
  have hhimem := (nvis k c s).max'_mem hne
  rw [mem_nvis_iff] at hlomem hhimem
  have hlt : (nvis k c s).min' hne < (nvis k c s).max' hne := by
    rcases Finset.card_eq_two.1 hs.2 with ⟨a, b, hab, hset⟩
    have ha : a ∈ nvis k c s := by rw [hset]; simp
    have hb : b ∈ nvis k c s := by rw [hset]; simp
    have h1 := Finset.min'_le _ _ ha
    have h2 := Finset.min'_le _ _ hb
    have h3 := Finset.le_max' _ _ ha
    have h4 := Finset.le_max' _ _ hb
    rcases lt_or_gt_of_ne hab with h | h <;> omega
  refine ⟨by omega, ?_, ?_, by omega, ?_, ?_⟩
  · rw [hlo]; omega
  · rw [hhi]; omega
  · rw [hlo]; exact hlomem.2
  · rw [hhi]; exact hhimem.2

/-- The *narrow* doubles: the doubles whose chord has both endpoints on the same side
(prefix or tail) of the run window (Section 5.3, `sec:surgery`). -/
def narrowDbl (k : ℕ) (c : ℕ → S) : Finset S :=
  (twiceSet k c).filter (fun s => dblHi k c s < k ∨ 2 * k + 6 ≤ dblLo k c s)

/-- The *wide* doubles: the doubles whose chord has one endpoint a prefix time and the
other a tail-side time (Section 5.3, `sec:surgery`). -/
def wideDbl (k : ℕ) (c : ℕ → S) : Finset S :=
  (twiceSet k c).filter (fun s => dblLo k c s < k ∧ 2 * k + 6 ≤ dblHi k c s)

/-- Every chord of a double is narrow or wide (Section 5.3, `sec:surgery`). -/
theorem twiceSet_subset_union : twiceSet k c ⊆ narrowDbl k c ∪ wideDbl k c := by
  intro s hs
  obtain ⟨hlt, hlo, hhi, hhin, -, -⟩ := dbl_chord hs
  rw [Finset.mem_union, narrowDbl, wideDbl, Finset.mem_filter, Finset.mem_filter]
  rcases hlo with h | h
  · rcases hhi with h' | h'
    · exact Or.inl ⟨hs, Or.inl h'⟩
    · exact Or.inr ⟨hs, h, h'⟩
  · exact Or.inl ⟨hs, Or.inr h⟩

/-- **Lemma 5.6(a),(c) (Narrow surgeries, `lem:narrow`)**, in counting form: there are at
most `ℓ-1` narrow chords.  Their lengths are nonzero modulo `ℓ` by (a) and pairwise
distinct modulo `ℓ` by (c). -/
theorem narrowDbl_card_le (hk : 18 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) (hd0le : Str.d0 + Str.ell ≤ 7) :
    (narrowDbl k c).card ≤ Str.ell - 1 := by
  classical
  have hk3 : 3 ≤ k := by omega
  have hell := Str.hell
  have hd0 := Str.d0_add
  have hmem : ∀ s ∈ narrowDbl k c,
      (dblHi k c s - dblLo k c s) % Str.ell ∈ Finset.Ico 1 Str.ell := by
    intro s hs
    rw [narrowDbl, Finset.mem_filter] at hs
    obtain ⟨hlt, hlo, hhi, hhin, hclo, hchi⟩ := dbl_chord hs.1
    rw [Finset.mem_Ico]
    refine ⟨?_, Nat.mod_lt _ (by omega)⟩
    by_contra hz
    have hdvd : Str.ell ∣ (dblHi k c s - dblLo k c s) := Nat.dvd_of_mod_eq_zero (by omega)
    have heq : c (dblLo k c s) = c (dblHi k c s) := by rw [hclo, hchi]
    rcases hs.2 with h | h
    · exact narrow_prefix_skip hk3 huaw Str hlt h heq hdvd
    · exact narrow_tail_skip hk3 huaw Str h hlt hhin heq hdvd
  have hinj : ∀ a ∈ narrowDbl k c, ∀ b ∈ narrowDbl k c,
      (dblHi k c a - dblLo k c a) % Str.ell = (dblHi k c b - dblLo k c b) % Str.ell →
        a = b := by
    intro a ha b hb hab
    by_contra hne
    have hma := hmem a ha
    rw [Finset.mem_Ico] at hma
    rw [narrowDbl, Finset.mem_filter] at ha hb
    obtain ⟨hlta, hloa, hhia, hhina, hcloa, hchia⟩ := dbl_chord ha.1
    obtain ⟨hltb, hlob, hhib, hhinb, hclob, hchib⟩ := dbl_chord hb.1
    have hlone : dblLo k c a ≠ dblLo k c b := by
      intro h; exact hne (by rw [← hcloa, ← hclob, h])
    have hea : c (dblLo k c a) = c (dblHi k c a) := by rw [hcloa, hchia]
    have heb : c (dblLo k c b) = c (dblHi k c b) := by rw [hclob, hchib]
    have hna : dblHi k c a < k ∨ (2 * k + 6 ≤ dblLo k c a ∧ dblHi k c a ≤ 3 * k + 7) := by
      rcases ha.2 with h | h
      exacts [Or.inl h, Or.inr ⟨h, hhina⟩]
    have hnb : dblHi k c b < k ∨ (2 * k + 6 ≤ dblLo k c b ∧ dblHi k c b ≤ 3 * k + 7) := by
      rcases hb.2 with h | h
      exacts [Or.inl h, Or.inr ⟨h, hhinb⟩]
    rcases lt_or_gt_of_ne hlone with h | h
    · exact narrow_pair_mod hk3 huaw Str (by omega) hlta hltb h hna hnb hea heb hab
    · exact narrow_pair_mod hk3 huaw Str (by omega) hltb hlta h hnb hna heb hea hab.symm
  have hcard := Finset.card_le_card_of_injOn
    (f := fun s => (dblHi k c s - dblLo k c s) % Str.ell)
    (s := narrowDbl k c) (t := Finset.Ico 1 Str.ell)
    (fun s hs => hmem s hs) (fun a ha b hb h => hinj a ha b hb h)
  simpa using hcard

/-- **Lemma 5.11 (`lem:Inonempty`)** of `ane-vs-an-separation-v4_1.tex`, in the form used
by the endgame: if `k ≥ 18` and the bookkeeping bounds `d₀ + ℓ ≤ 7` and `b₁ + s₀ + 2ℓ ≤ 8`
of `eq:dzero` hold, then some index `i ≤ k-1` is *aligned*, i.e. `g_i = h_i`. -/
theorem exists_aligned_index (hk : 18 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) (hell4 : Str.ell ≤ 4) (hd0le : Str.d0 + Str.ell ≤ 7)
    (hbs : bridgeCount k c + singleCount k c + 2 * Str.ell ≤ 8) :
    ∃ i, i < k ∧ c i = c (2 * k + 6 + i) := by
  classical
  by_contra hcon
  push_neg at hcon
  have hk3 : 3 ≤ k := by omega
  have hell := Str.hell
  have hd0 := Str.d0_add
  have htl : k - 1 ≤ Str.tt * Str.ell := by omega
  -- the doubles, split into the narrow and the wide ones
  set Nar : Finset S := narrowDbl k c with hNar
  set Wid : Finset S := wideDbl k c with hWid
  have hsplit : twiceSet k c ⊆ Nar ∪ Wid := twiceSet_subset_union
  -- (1) at most `ℓ-1` narrow chords
  have hnar : Nar.card ≤ Str.ell - 1 := narrowDbl_card_le hk huaw Str hd0le
  -- (2) at most `3ℓ` wide chords
  have hwid : Wid.card ≤ 3 * Str.ell := by
    set sh : S → ℕ := fun s => (dblHi k c s - (2 * k + 6)) + (k - 1 - dblLo k c s) with hsh
    have hmem : ∀ s ∈ Wid, (sh s % Str.ell, sh s / k) ∈
        (Finset.range Str.ell) ×ˢ (Finset.range 3) := by
      intro s hs
      rw [hWid, wideDbl, Finset.mem_filter] at hs
      obtain ⟨hlt, hlo, hhi, hhin, hclo, hchi⟩ := dbl_chord hs.1
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
      refine ⟨Nat.mod_lt _ (by omega), ?_⟩
      have hlok := hs.2.1
      have hhik := hs.2.2
      have hbound : sh s < 3 * k := by simp only [hsh]; omega
      exact Nat.div_lt_of_lt_mul (by omega)
    have hinj : ∀ a ∈ Wid, ∀ b ∈ Wid,
        (sh a % Str.ell, sh a / k) = (sh b % Str.ell, sh b / k) → a = b := by
      intro a ha b hb hab
      by_contra hne
      have hres : sh a % Str.ell = sh b % Str.ell := congrArg Prod.fst hab
      have hbuc : sh a / k = sh b / k := congrArg Prod.snd hab
      rw [hWid, wideDbl, Finset.mem_filter] at ha hb
      obtain ⟨hlta, hloa, hhia, hhina, hcloa, hchia⟩ := dbl_chord ha.1
      obtain ⟨hltb, hlob, hhib, hhinb, hclob, hchib⟩ := dbl_chord hb.1
      have hlone : dblLo k c a ≠ dblLo k c b := by
        intro h; exact hne (by rw [← hcloa, ← hclob, h])
      have hhine : dblHi k c a ≠ dblHi k c b := by
        intro h; exact hne (by rw [← hchia, ← hchib, h])
      -- the two chords, listed in the order of their prefix indices
      have main : ∀ x y : S,
          dblLo k c x < k → 2 * k + 6 ≤ dblHi k c x →
          dblLo k c y < k → 2 * k + 6 ≤ dblHi k c y →
          dblHi k c x ≤ 3 * k + 7 → dblHi k c y ≤ 3 * k + 7 →
          c (dblLo k c x) = x → c (dblHi k c x) = x →
          c (dblLo k c y) = y → c (dblHi k c y) = y →
          dblLo k c x < dblLo k c y → dblHi k c x ≠ dblHi k c y →
          sh x % Str.ell = sh y % Str.ell → sh x / k = sh y / k → False := by
        intro x y hxlo hxhi hylo hyhi hxn hyn hcx1 hcx2 hcy1 hcy2 hlt2 hhine2 hres2 hbuc2
        set jx := dblLo k c x with hjx
        set jy := dblLo k c y with hjy
        set jx' := dblHi k c x - (2 * k + 6) with hjx'
        set jy' := dblHi k c y - (2 * k + 6) with hjy'
        have hxeq : c jx = c (2 * k + 6 + jx') := by
          rw [hcx1, show 2 * k + 6 + jx' = dblHi k c x by omega, hcx2]
        have hyeq : c jy = c (2 * k + 6 + jy') := by
          rw [hcy1, show 2 * k + 6 + jy' = dblHi k c y by omega, hcy2]
        -- the tail indices decrease (Lemma 5.7(i), `lem:wide`, plus `I = ∅`)
        have hgt : jy' < jx' := by
          rcases Nat.lt_trichotomy jx' jy' with h | h | h
          · obtain ⟨hax, -⟩ :=
              wide_chords_nested hk3 huaw hlt2 hylo h (by omega) hxeq hyeq
            rw [hax] at hxeq
            exact absurd hxeq (hcon jx hxlo)
          · omega
          · exact h
        -- the shifts differ by `D`, which is `< k` and divisible by `ℓ`
        have hshx : sh x = jx' + (k - 1 - jx) := rfl
        have hshy : sh y = jy' + (k - 1 - jy) := rfl
        have hD : sh y + ((jx' - jy') + (jy - jx)) = sh x := by omega
        have hdvd : Str.ell ∣ ((jx' - jy') + (jy - jx)) := by
          have hmodeq : sh y % Str.ell = sh x % Str.ell := hres2.symm
          have hle' : sh y ≤ sh x := by omega
          have hdd := (Nat.modEq_iff_dvd' hle').mp hmodeq
          rwa [show sh x - sh y = (jx' - jy') + (jy - jx) by omega] at hdd
        have hlt3 : (jx' - jy') + (jy - jx) < k := by
          have h1 := Nat.div_add_mod (sh x) k
          have h2 := Nat.div_add_mod (sh y) k
          have h3 : sh x % k < k := Nat.mod_lt _ (by omega)
          have h4 : sh y % k < k := Nat.mod_lt _ (by omega)
          rw [hbuc2] at h1
          omega
        exact wide_chord_fold hk3 huaw Str (ja := jx) (jb := jy) (ja' := jx') (jb' := jy')
          hlt2 hylo (by omega) hgt hxeq.symm hyeq hdvd (by omega)
      rcases lt_or_gt_of_ne hlone with h | h
      · exact main a b ha.2.1 ha.2.2 hb.2.1 hb.2.2 hhina hhinb hcloa hchia hclob
          hchib h hhine hres hbuc
      · exact main b a hb.2.1 hb.2.2 ha.2.1 ha.2.2 hhinb hhina hclob hchib hcloa
          hchia h (Ne.symm hhine) hres.symm hbuc.symm
    have hcard := Finset.card_le_card_of_injOn
      (f := fun s => (sh s % Str.ell, sh s / k))
      (s := Wid) (t := (Finset.range Str.ell) ×ˢ (Finset.range 3))
      (fun s hs => hmem s hs) (fun a ha b hb h => hinj a ha b hb h)
    simpa [Finset.card_product, Nat.mul_comm] using hcard
  -- (3) the count `2k+2 = 2f + b₁ + s₀ ≤ 6ℓ+6 ≤ 30`
  have hcards : (twiceSet k c).card ≤ Nar.card + Wid.card :=
    le_trans (Finset.card_le_card hsplit) (Finset.card_union_le _ _)
  have h1 := count_nonrun hk3 huaw
  have h2 := card_onceSet hk3 huaw
  omega

end

end AneVsAn
