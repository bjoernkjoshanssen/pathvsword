import RequestProject.WalkChordPair

/-!
# Two odd chords, general position (Lemma 5.14(b), `lem:twoodd`)

`RequestProject/WalkChordPair.lean` proves Lemma 5.14(a) (`lem:twoodd`) of
`ane-vs-an-separation-v4_1.tex`: for `ℓ = 2` two bridges make the walk non uniquely
accepting.  The present file extends the case analysis to part (b), where one of the two
chords is a *narrow* chord (of odd length) instead of a bridge chord.

The classification of the position of a chord relative to the stretch `S = [p,q]` used in
the source ("early", "wide", "late") becomes the five-fold `ChordKind`: a narrow prefix
chord and an early bridge chord are treated alike (`low`), a narrow tail chord and a late
bridge chord differ only in that the former starts after the `c`-edge (`high` vs. late).
Two further candidate paths are needed for a chord of the last kind:

* `chord_pair_A6` — the candidate `π_A` whose first segment `W[0,a₁]⟨u⟩` reaches into the
  tail, with a spin adjustment in the first and the last segment;
* `chord_pair_A7` — the same with a spin adjustment in the first segment only.

Both use the new non-triviality test `chord_path_span`, which generalizes
`chord_path_spin` by comparing the letters at an arbitrary junction position.

The file concludes with

* `narrow_chord_data` — the chord of a narrow double, with its parity, its endpoint
  letters and its `ChordKind`;
* `no_narrow_of_bridge` — **Lemma 6.6(e) (`lem:parity2`)**: in the bridge shape there is
  no narrow chord at all.
-/

namespace AneVsAn

set_option autoImplicit false

section

variable {k : ℕ} {S : Type} {c : ℕ → S}

/-- **Lemma 5.14 (`lem:twoodd`), fourth non-triviality test.**  A candidate path whose
first segment is a spin adjusted traversal `W[0,A]⟨u⟩` differs from `W` as soon as the
letter read by the next edge differs from the letter `W` reads at the junction position
`|W[0,A]⟨u⟩|`.  This is `chord_path_spin` without the assumption that the junction lies
inside the run window. -/
theorem chord_path_span (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) {A B L2 L3 u : ℕ} {τ2 τ3 : ℕ → ℕ} {s : S}
    (hqA : Str.q ≤ A) (hAn : A ≤ 3 * k + 7)
    (h2 : Seg k c (c A) s L2 τ2) (h3 : Seg k c s (c (3 * k + 7)) L3 τ3)
    (hL2 : 0 < L2) (hτ2 : τ2 0 = B)
    (hlen : Str.slen 0 A u + (L2 + L3) = 3 * k + 7)
    (hne : zw k B ≠ zw k (Str.slen 0 A u)) : False := by
  obtain ⟨τ1, h1, -, -, -⟩ := spanSegI Str (Nat.zero_le _) hqA hAn u
  have hall := seg_cat h1 (seg_cat h2 h3)
  rw [hlen] at hall
  refine no_second_path hk huaw hall (j := Str.slen 0 A u) (by omega) ?_
  have hv : cat (Str.slen 0 A u) τ1 (cat L2 τ2 τ3) (Str.slen 0 A u) = B := by
    rw [cat_ge (by omega), Nat.sub_self, cat_lt hL2, hτ2]
  rw [hv]
  exact hne

/-- **Lemma 5.14 (`lem:twoodd`)**, the candidate `π_A` whose first segment `W[0,a₁]⟨u₁⟩`
reaches into the tail, with a spin adjustment in the first and the last segment (`N = 2`).
The moved `c`-edge of the first segment provides the non-triviality.  Used when `a` is a
narrow tail chord and `b` is a wide tail chord. -/
theorem chord_pair_A6 (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) {a₁ a₂ b₁ b₂ : ℕ}
    (ha16 : 2 * k + 6 ≤ a₁) (ha : a₁ < a₂) (ha2n : a₂ ≤ 3 * k + 7)
    (hb1p : b₁ ≤ Str.p) (hb : b₁ < b₂) (hb2 : b₂ ≤ 3 * k + 7) (hab : a₂ ≤ b₂)
    (hca : c a₁ = c a₂) (hcb : c b₁ = c b₂)
    (hdvd : Str.ell ∣ ((b₂ - b₁) - (a₂ - a₁)))
    (hpos : 0 < (b₂ - b₁) - (a₂ - a₁))
    (hcap : (b₂ - b₁) - (a₂ - a₁) ≤ 2 * (Str.tt * Str.ell)) : False := by
  have hq := Str.hq
  have hp := Str.hp
  have hell := Str.hell
  have hlenS := Str.hlen
  obtain ⟨u1, u3, hu, hu1, hu1'⟩ := exists_turns_down Str hdvd hcap
  have hu1lt := hu1' hpos
  have hmul : (u1 + 1) * Str.ell ≤ Str.tt * Str.ell := Nat.mul_le_mul (by omega) (le_refl _)
  have hexp : (u1 + 1) * Str.ell = u1 * Str.ell + Str.ell := by ring
  have hs1 := Str.slen_eq (Nat.zero_le _) (show Str.q ≤ a₁ by omega) u1
  have hs3 := Str.slen_eq hb1p (show Str.q ≤ 3 * k + 7 by omega) u3
  have hlen : Str.slen 0 a₁ u1 + ((b₂ - a₂) + Str.slen b₁ (3 * k + 7) u3) = 3 * k + 7 := by
    omega
  have h2 : Seg k c (c a₂) (c b₂) (b₂ - a₂) (fun t => a₂ + t) := segW c hab hb2
  rw [← hca] at h2
  obtain ⟨τ3, h3⟩ := Str.spanSeg hb1p (show Str.q ≤ 3 * k + 7 by omega) (le_refl _) u3
  rw [hcb] at h3
  exact chord_path_cedge hk huaw Str ha16 (by omega) h2 h3 hlen (by omega)

/-- **Lemma 5.14 (`lem:twoodd`)**, the candidate `π_A` whose first segment `W[0,a₁]⟨u⟩`
reaches into the tail, with a spin adjustment in the first segment only.  Used when `a` is
a narrow tail chord and `b` lies after the stretch.  If the adjustment is trivial the two
chords have equal length and the junction letters do the job; otherwise the moved
`c`-edge does. -/
theorem chord_pair_A7 (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) {a₁ a₂ b₁ b₂ : ℕ}
    (ha16 : 2 * k + 6 ≤ a₁) (ha : a₁ < a₂) (ha2n : a₂ ≤ 3 * k + 7)
    (hb : b₁ < b₂) (hb2 : b₂ ≤ 3 * k + 7) (hab : a₂ < b₂)
    (hca : c a₁ = c a₂) (hcb : c b₁ = c b₂) (hltr : zw k a₂ ≠ zw k a₁)
    (hd1 : Str.ell ∣ ((a₂ - a₁) - (b₂ - b₁))) (hd2 : Str.ell ∣ ((b₂ - b₁) - (a₂ - a₁)))
    (hcap : (b₂ - b₁) - (a₂ - a₁) ≤ Str.tt * Str.ell) : False := by
  have hq := Str.hq
  have hp := Str.hp
  have hell := Str.hell
  have hlenS := Str.hlen
  obtain ⟨u, hu⟩ : ∃ u, u * Str.ell + (b₂ - b₁) = Str.tt * Str.ell + (a₂ - a₁) := by
    rcases Nat.le_total (b₂ - b₁) (a₂ - a₁) with h | h
    · obtain ⟨u, hu⟩ := exists_turn_up Str hd1
      exact ⟨u, by omega⟩
    · obtain ⟨u, hu⟩ := exists_turn_down Str hd2 hcap
      exact ⟨u, by omega⟩
  have hs1 := Str.slen_eq (Nat.zero_le _) (show Str.q ≤ a₁ by omega) u
  have hlen : Str.slen 0 a₁ u + ((b₂ - a₂) + (3 * k + 7 - b₁)) = 3 * k + 7 := by omega
  have h2 : Seg k c (c a₂) (c b₂) (b₂ - a₂) (fun t => a₂ + t) := segW c (by omega) hb2
  rw [← hca] at h2
  have h3 : Seg k c (c b₁) (c (3 * k + 7)) (3 * k + 7 - b₁) (fun t => b₁ + t) :=
    segW c (by omega) (by omega)
  rw [hcb] at h3
  by_cases hut : u = Str.tt
  · subst hut
    have hslen : Str.slen 0 a₁ Str.tt = a₁ := by
      rw [Str.slen_tt (Nat.zero_le _) (by omega)]
      omega
    refine chord_path_span hk huaw Str (show Str.q ≤ a₁ by omega) (by omega) h2 h3
      (by omega) rfl hlen ?_
    rw [hslen]
    exact hltr
  · refine chord_path_cedge hk huaw Str ha16 (by omega) h2 h3 hlen ?_
    have hne : u * Str.ell ≠ Str.tt * Str.ell := fun h =>
      hut (Nat.eq_of_mul_eq_mul_right (by omega) h)
    omega

/-- **Lemma 5.14 (`lem:twoodd`)**, the candidate `π_A` with a spin adjustment in the first
segment only, in the case where the junction may fall behind the `c`-edge.  Used when `a`
is a late bridge chord and `b` is a narrow tail chord: the junction sits at
`a₂ - L_b`, a position of the run window or of the tail, and in both cases the letter read
there by `W` differs from `z_{a₂}`. -/
theorem chord_pair_A8 (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) {a₁ a₂ b₁ b₂ : ℕ}
    (hqa1 : Str.q ≤ a₁) (ha : a₁ < a₂) (ha26 : 2 * k + 6 ≤ a₂)
    (ha2 : a₂ ≤ 3 * k + 5) (hb16 : 2 * k + 6 ≤ b₁) (hb : b₁ < b₂) (hb2 : b₂ ≤ 3 * k + 7)
    (hab : a₂ < b₂) (hlb : b₂ - b₁ ≤ k + 1)
    (hca : c a₁ = c a₂) (hcb : c b₁ = c b₂)
    (hd1 : Str.ell ∣ ((a₂ - a₁) - (b₂ - b₁))) (hd2 : Str.ell ∣ ((b₂ - b₁) - (a₂ - a₁)))
    (hcap : (b₂ - b₁) - (a₂ - a₁) ≤ Str.tt * Str.ell) : False := by
  have hq := Str.hq
  have hp := Str.hp
  obtain ⟨u, hu⟩ : ∃ u, u * Str.ell + (b₂ - b₁) = Str.tt * Str.ell + (a₂ - a₁) := by
    rcases Nat.le_total (b₂ - b₁) (a₂ - a₁) with h | h
    · obtain ⟨u, hu⟩ := exists_turn_up Str hd1
      exact ⟨u, by omega⟩
    · obtain ⟨u, hu⟩ := exists_turn_down Str hd2 hcap
      exact ⟨u, by omega⟩
  have hs1 := Str.slen_eq (Nat.zero_le _) hqa1 u
  have hJ : Str.slen 0 a₁ u = a₂ - (b₂ - b₁) := by omega
  have hlen : Str.slen 0 a₁ u + ((b₂ - a₂) + (3 * k + 7 - b₁)) = 3 * k + 7 := by omega
  have h2 : Seg k c (c a₂) (c b₂) (b₂ - a₂) (fun t => a₂ + t) := segW c (by omega) hb2
  rw [← hca] at h2
  have h3 : Seg k c (c b₁) (c (3 * k + 7)) (3 * k + 7 - b₁) (fun t => b₁ + t) :=
    segW c (by omega) (by omega)
  rw [hcb] at h3
  refine chord_path_span hk huaw Str hqa1 (by omega) h2 h3 (by omega) rfl hlen ?_
  rw [hJ]
  rcases (by omega : a₂ - (b₂ - b₁) ≤ 2 * k + 5 ∨ 2 * k + 6 ≤ a₂ - (b₂ - b₁)) with h | h
  · exact zw_run_ne hk (Or.inr ha26) (by omega) h
  · exact (zw_tail_ne hk (by omega) (by omega) (by omega)).symm

/-! ### The five positions of a chord relative to the stretch -/

/-- The position of a chord `(x,y)` relative to the stretch `S = [p,q]`, in the form used
by Lemma 5.14 (`lem:twoodd`) for `ℓ = 2`.  A chord is *low* (its interval lies before `S`;
this covers the narrow prefix chords and the early bridge chords), *wide* on the prefix or
on the tail side, *late* (a bridge chord starting inside the run window and ending in the
tail) or *high* (a narrow tail chord).  The length bounds are `eq:bridgelen` for the
bridge chords and `λ ≤ k+1` for the narrow chords. -/
def ChordKind (Str : Stretch k c) (x y : ℕ) : Prop :=
  (x < k ∧ y < Str.p ∧ y - x ≤ k + 1) ∨
  (x < k ∧ Str.q < y ∧ y ≤ 2 * k + 5 ∧ k + 2 ≤ y - x ∧ y - x ≤ k + 11) ∨
  (k ≤ x ∧ x < Str.p ∧ 2 * k + 6 ≤ y ∧ y ≤ 3 * k + 5 ∧ k + 2 ≤ y - x ∧ y - x ≤ k + 11) ∨
  (Str.q < x ∧ x ≤ 2 * k + 5 ∧ 2 * k + 6 ≤ y ∧ y ≤ 3 * k + 5 ∧ y - x ≤ 10) ∨
  (2 * k + 6 ≤ x ∧ y ≤ 3 * k + 7 ∧ y - x ≤ k + 1)

/-- A bridge chord is a chord in the sense of `ChordKind`. -/
theorem chordKind_of_bridge (hk : 18 ≤ k) (Str : Stretch k c) {x y : ℕ}
    (h : BridgeChordKind Str x y) : ChordKind Str x y := by
  simp only [BridgeChordKind, ChordKind] at h ⊢
  rcases h with h | h | h | h
  · exact Or.inl ⟨by omega, by omega, by omega⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

/-- **Lemma 5.14 (Two odd chords, `lem:twoodd`)**, the ordered form for arbitrary chords:
the case analysis of the source, after the chords have been named so that `a₂ < b₂`.  In
each possible position of the two chords one of the candidate paths `π_A`, `π_D` of the
source, completed by a spin adjustment, is a second accepting path of length `n`. -/
theorem two_chords_ordered (hk : 18 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) (hell : Str.ell = 2) (hT : k ≤ Str.tt * Str.ell)
    {a₁ a₂ b₁ b₂ : ℕ} (ha : a₁ < a₂) (hb : b₁ < b₂)
    (hca : c a₁ = c a₂) (hcb : c b₁ = c b₂) (hltr : zw k a₂ ≠ zw k a₁)
    (hoa : (a₂ - a₁) % 2 = 1) (hob : (b₂ - b₁) % 2 = 1)
    (ka : ChordKind Str a₁ a₂) (kb : ChordKind Str b₁ b₂)
    (hord : a₂ < b₂) : False := by
  have hp := Str.hp
  have hq := Str.hq
  have hlenS := Str.hlen
  have hpq : Str.p ≤ Str.q := by omega
  simp only [ChordKind] at ka kb
  rcases ka with ka | ka | ka | ka | ka
  · -- `a` is low
    rcases kb with kb | kb | kb | kb | kb
    · exact chord_pair_A1 (by omega) huaw Str ha hb hord (by omega) (by omega) hca hcb
        hltr (by rw [hell]; omega) (by rw [hell]; omega) (by omega)
    · exact chord_pair_A2 (by omega) huaw Str ha hb (by omega) (by omega) (by omega)
        (by omega) hca hcb hltr (by omega) (by rw [hell]; omega) (by omega)
    · exact chord_pair_A2 (by omega) huaw Str ha hb (by omega) (by omega) (by omega)
        (by omega) hca hcb hltr (by omega) (by rw [hell]; omega) (by omega)
    · exact chord_pair_A3 (by omega) huaw Str ha hb (by omega) (by omega) (by omega)
        (by omega) hca hcb hltr (by rw [hell]; omega) (by rw [hell]; omega) (by omega)
    · exact chord_pair_A3 (by omega) huaw Str ha hb (by omega) (by omega) (by omega)
        (by omega) hca hcb hltr (by rw [hell]; omega) (by rw [hell]; omega) (by omega)
  · -- `a` is a wide prefix chord
    rcases kb with kb | kb | kb | kb | kb
    · exact absurd hord (by omega)
    · exact chord_pair_A1 (by omega) huaw Str ha hb hord (by omega) (by omega) hca hcb
        hltr (by rw [hell]; omega) (by rw [hell]; omega) (by omega)
    · exact chord_pair_A1 (by omega) huaw Str ha hb hord (by omega) (by omega) hca hcb
        hltr (by rw [hell]; omega) (by rw [hell]; omega) (by omega)
    · exact chord_pair_D1 (by omega) huaw Str (by omega) (by omega) (by omega) ha
        (by omega) hb (by omega) hca hcb (by omega) (by rw [hell]; omega) (by omega)
    · exact chord_pair_D1 (by omega) huaw Str (by omega) (by omega) (by omega) ha
        (by omega) hb (by omega) hca hcb (by omega) (by rw [hell]; omega) (by omega)
  · -- `a` is a wide tail chord
    rcases kb with kb | kb | kb | kb | kb
    · exact absurd hord (by omega)
    · exact absurd hord (by omega)
    · exact chord_pair_A1 (by omega) huaw Str ha hb hord (by omega) (by omega) hca hcb
        hltr (by rw [hell]; omega) (by rw [hell]; omega) (by omega)
    · exact chord_pair_D2 (by omega) huaw Str (by omega) (by omega) (by omega)
        (by omega) hb (by omega) hca hcb (by rw [hell]; omega) (by omega) (by omega)
    · exact chord_pair_D2 (by omega) huaw Str (by omega) (by omega) (by omega)
        (by omega) hb (by omega) hca hcb (by rw [hell]; omega) (by omega) (by omega)
  · -- `a` is a late bridge chord
    rcases kb with kb | kb | kb | kb | kb
    · exact absurd hord (by omega)
    · exact absurd hord (by omega)
    · exact chord_pair_A4 (by omega) huaw Str (by omega) (by omega) ha (by omega) hb
        hord (by omega) (by omega) hca hcb (by omega) (by rw [hell]; omega) (by omega)
    · exact chord_pair_A5 (by omega) huaw Str (by omega) (by omega) ha (by omega) hb
        hord (by omega) (by omega) hca hcb (by rw [hell]; omega) (by rw [hell]; omega)
        (by omega)
    · exact chord_pair_A8 (by omega) huaw Str (by omega) ha (by omega)
        (by omega) (by omega) hb (by omega) hord (by omega) hca hcb
        (by rw [hell]; omega) (by rw [hell]; omega) (by omega)
  · -- `a` is a narrow tail chord
    rcases kb with kb | kb | kb | kb | kb
    · exact absurd hord (by omega)
    · exact absurd hord (by omega)
    · exact chord_pair_A6 (by omega) huaw Str (by omega) ha (by omega) (by omega) hb
        (by omega) (by omega) hca hcb (by rw [hell]; omega) (by omega) (by omega)
    · exact chord_pair_A7 (by omega) huaw Str (by omega) ha (by omega) hb
        (by omega) hord hca hcb hltr (by rw [hell]; omega) (by rw [hell]; omega)
        (by omega)
    · exact chord_pair_A7 (by omega) huaw Str (by omega) ha (by omega) hb
        (by omega) hord hca hcb hltr (by rw [hell]; omega) (by rw [hell]; omega)
        (by omega)

/-- **Lemma 5.14 (Two odd chords, `lem:twoodd`)**, general form: for `ℓ = 2`, two chords
of odd length whose right endpoints differ make `W` non uniquely accepting.  This is the
form in which parts (a) and (b) of the source are used. -/
theorem two_chords (hk : 18 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) (hell : Str.ell = 2) (hT : k ≤ Str.tt * Str.ell)
    {a₁ a₂ b₁ b₂ : ℕ} (ha : a₁ < a₂) (hb : b₁ < b₂)
    (hca : c a₁ = c a₂) (hcb : c b₁ = c b₂)
    (hltra : zw k a₂ ≠ zw k a₁) (hltrb : zw k b₂ ≠ zw k b₁)
    (hoa : (a₂ - a₁) % 2 = 1) (hob : (b₂ - b₁) % 2 = 1) (hne : a₂ ≠ b₂)
    (ka : ChordKind Str a₁ a₂) (kb : ChordKind Str b₁ b₂) : False := by
  rcases Nat.lt_or_ge a₂ b₂ with h | h
  · exact two_chords_ordered hk huaw Str hell hT ha hb hca hcb hltra hoa hob ka kb h
  · exact two_chords_ordered hk huaw Str hell hT hb ha hcb hca hltrb hob hoa kb ka
      (by omega)

end

section

variable {k : ℕ} {S : Type} [DecidableEq S] {c : ℕ → S}

/-- **The chord of a narrow double**, for `ℓ = 2`.  Its length is not divisible by `ℓ`
(Lemma 5.6(a), `lem:narrow`), hence odd; its two endpoints carry distinct letters (two
prefix letters, or two tail-side letters, the pair `(3k+6, 3k+7)` being excluded by
Lemma 5.10(f), `lem:positions`); and its position relative to the stretch is `low` or
`high`. -/
theorem narrow_chord_data (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) (hell : Str.ell = 2) {s : S} (hs : s ∈ narrowDbl k c) :
    ∃ x z, x < z ∧ c x = s ∧ c z = s ∧ (z - x) % 2 = 1 ∧ zw k z ≠ zw k x ∧
      ChordKind Str x z := by
  have hp := Str.hp
  rw [narrowDbl, Finset.mem_filter] at hs
  obtain ⟨hst, hside⟩ := hs
  obtain ⟨hlt, hlo, hhi, hhin, hclo, hchi⟩ := dbl_chord hst
  refine ⟨dblLo k c s, dblHi k c s, hlt, hclo, hchi, ?_, ?_, ?_⟩
  · by_contra hcon
    have hdvd : Str.ell ∣ (dblHi k c s - dblLo k c s) := by rw [hell]; omega
    have heq : c (dblLo k c s) = c (dblHi k c s) := by rw [hclo, hchi]
    rcases hside with h | h
    · exact narrow_prefix_skip hk huaw Str hlt h heq hdvd
    · exact narrow_tail_skip hk huaw Str h hlt hhin heq hdvd
  · rcases hside with h | h
    · rw [zw_a (show dblHi k c s < k by omega), zw_a (show dblLo k c s < k by omega)]
      simp only [ne_eq, Ltr.a.injEq]
      omega
    · rcases (by omega : dblHi k c s ≤ 3 * k + 6 ∨ dblHi k c s = 3 * k + 7) with h' | h'
      · exact (zw_tail_ne hk (by omega) hlt h').symm
      · rcases (by omega : dblLo k c s < 3 * k + 6 ∨ dblLo k c s = 3 * k + 6) with h'' | h''
        · have he7 : zw k (3 * k + 7) = Ltr.e := by
            simp only [zw, if_neg (by omega : ¬ (3 * k + 7 : ℕ) < k),
              if_neg (by omega : ¬ (3 * k + 7 : ℕ) < 2 * k + 5),
              if_neg (by omega : ¬ (3 * k + 7 : ℕ) = 2 * k + 5),
              if_neg (by omega : ¬ (3 * k + 7 : ℕ) < 3 * k + 5),
              if_neg (by omega : ¬ (3 * k + 7 : ℕ) = 3 * k + 5)]
          rw [h', he7]
          rcases (by omega : dblLo k c s < 3 * k + 5 ∨ dblLo k c s = 3 * k + 5)
            with h3 | h3
          · rw [zw_a' (by omega) h3]; simp
          · rw [zw_d (by omega) h3]; simp
        · exact absurd (by rw [← h'', ← h', hclo, hchi] :
            c (3 * k + 6) = c (3 * k + 7)) (fun hcon =>
              positions_u1_ne_u2 hk huaw Str hcon)
  · simp only [ChordKind]
    rcases hside with h | h
    · exact Or.inl ⟨by omega, by omega, by omega⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega, by omega⟩)))

/-- **Lemma 6.6(e) (`lem:parity2`)**: in the bridge shape (`ℓ = 2` and `b₁ ≥ 1`) there is
no narrow chord: a narrow chord has odd length by Lemma 5.6(a) (`lem:narrow`) and the
bridge chord has odd length by Lemma 5.13 (`lem:bridgeparity`), so Lemma 5.14(b)
(`lem:twoodd`) applies. -/
theorem no_narrow_of_bridge (hk : 18 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) (hell : Str.ell = 2) (hd0le : Str.d0 + Str.ell ≤ 7)
    (hbs : bridgeCount k c + singleCount k c + 2 * Str.ell ≤ 8)
    (hmax : ∀ u, u ≤ 3 * k + 7 →
      (∃ x, Str.p ≤ x ∧ x < Str.p + Str.ell ∧ c x = c u) → Str.p ≤ u ∧ u ≤ Str.q)
    (hb : 1 ≤ bridgeCount k c) : narrowDbl k c = ∅ := by
  classical
  by_contra hcon
  obtain ⟨s, hs⟩ := Finset.nonempty_of_ne_empty hcon
  obtain ⟨y, hy⟩ := Finset.card_pos.1 (show 0 < ((onceSet k c).filter
    (fun s => (rvis k c s).card = 1)).card by rw [← bridgeCount]; omega)
  rw [Finset.mem_filter] at hy
  obtain ⟨a₁, a₂, ha, hca1, hca2, hoa, hltra, ka⟩ :=
    bridge_chord_data hk huaw Str hell hd0le hbs hmax hy.1 hy.2
  obtain ⟨b₁, b₂, hb', hcb1, hcb2, hob, hltrb, kb⟩ :=
    narrow_chord_data (by omega) huaw Str hell hs
  have hdd := Str.d0_add
  have hT : k ≤ Str.tt * Str.ell := by omega
  refine two_chords hk huaw Str hell hT ha hb' (by rw [hca1, hca2])
    (by rw [hcb1, hcb2]) hltra hltrb hoa hob ?_ (chordKind_of_bridge hk Str ka) kb
  intro hne
  -- the two states would coincide, but one has one non-run visit and the other two
  have hys : y = s := by rw [← hca2, hne, hcb2]
  rw [onceSet, Finset.mem_filter] at hy
  have hs2 : s ∈ twiceSet k c := narrowDbl_subset_twice hs
  rw [twiceSet, Finset.mem_filter] at hs2
  rw [hys] at hy
  omega

end

end AneVsAn
