import RequestProject.WalkSurgery

/-!
# Wide chords and position constraints (Sections 5.3–5.4 of `anevsanseparationv4.tex`)

This file collects the consequences of the Crossing Lemma 4.7 (`lem:cross`) for the
various kinds of chords of a hypothetical `(k+5)`-state uniquely accepting walk:

* `wide_chords_nested` — Lemma 5.7(i) (`lem:wide`): two wide chords with increasing
  prefix indices and increasing tail indices must both be aligned;
* `positions_wide_not_below`, `positions_wide_not_above` — Lemma 5.10(a)
  (`lem:positions`);
* `positions_PU`, `positions_TU` — Lemma 5.10(b),(c);
* `positions_PP`, `positions_TT` — Lemma 5.10(d);
* `positions_prefix_bridge`, `positions_tail_bridge`, `positions_u_not_bridge` —
  Lemma 5.10(e);
* `positions_u1_ne_u2`, `positions_PU_TU_incompatible` — Lemma 5.10(f).

Throughout, an *aligned index* is an `i < k` with `c i = c (2k+6+i)` (the chords of
length `δ₀ = 2k+6` of Lemma 4.6, `lem:block`).
-/

namespace AneVsAn

set_option autoImplicit false

section

variable {k : ℕ} {S : Type} {c : ℕ → S}

/-- Two distinct positions in the closed tail window `[2k+5, 3k+6]` carry distinct
letters of `z_k`.  (These are the letters `c, a_1, …, a_{k-1}, d, e`, "all pairwise
distinct" as recorded at the start of Section 5.3 of `anevsanseparationv4.tex`.) -/
theorem zw_tail_ne (hk : 3 ≤ k) {x y : ℕ} (hx : 2 * k + 5 ≤ x) (hxy : x < y)
    (hy : y ≤ 3 * k + 6) : zw k x ≠ zw k y := by
  intro h
  rcases zw_eq_cases hk hxy (by omega) h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

/-- **Lemma 5.7(i) (Wide chords, `lem:wide`)**: if the wide chords `(j_a,j'_a)` and
`(j_b,j'_b)` satisfy `j_a < j_b` and `j'_a < j'_b`, then unless the walk fails to be
uniquely accepting both chords are aligned, i.e. `j'_a = j_a` and `j'_b = j_b`. -/
theorem wide_chords_nested (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    {ja jb ja' jb' : ℕ} (hab : ja < jb) (hbk : jb < k) (ha'b' : ja' < jb')
    (hb'k : jb' ≤ k + 1)
    (heqa : c ja = c (2 * k + 6 + ja')) (heqb : c jb = c (2 * k + 6 + jb')) :
    ja' = ja ∧ jb' = jb := by
  obtain ⟨h1, h2⟩ := crossing hk huaw (a₁ := ja) (b₁ := jb) (a₂ := 2 * k + 6 + ja')
    (b₂ := 2 * k + 6 + jb') (by omega) (by omega) (by omega) (by omega) heqa heqb
  constructor
  · rw [zw_a (show ja < k by omega)] at h1
    rcases (by omega : ja' + 1 < k ∨ ja' + 1 = k ∨ ja' = k) with h | h | h
    · rw [zw_a' (by omega) (by omega)] at h1
      simp only [Ltr.a.injEq] at h1; omega
    · rw [zw_d (by omega) (by omega)] at h1; exact absurd h1 (by simp)
    · rw [zw_e (by omega)] at h1; exact absurd h1 (by simp)
  · rw [zw_a (show jb - 1 < k by omega), show 2 * k + 6 + jb' - 1 = 2 * k + 5 + jb' by omega]
      at h2
    rcases (by omega : jb' = 0 ∨ (1 ≤ jb' ∧ jb' < k) ∨ jb' = k ∨ jb' = k + 1)
      with h | h | h | h
    · rw [zw_c (by omega)] at h2; exact absurd h2 (by simp)
    · rw [zw_a' (by omega) (by omega)] at h2
      simp only [Ltr.a.injEq] at h2; omega
    · rw [zw_d (by omega) (by omega)] at h2; exact absurd h2 (by simp)
    · rw [zw_e (by omega)] at h2; exact absurd h2 (by simp)

/-- **Lemma 5.10(a) (Position constraints, `lem:positions`)**, first half: a non-aligned
wide chord `(j,j')` with `j, j' ≤ k-1` cannot have both indices strictly below an aligned
index `i`. -/
theorem positions_wide_not_below (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    {i j j' : ℕ} (hik : i < k) (halign : c i = c (2 * k + 6 + i))
    (hji : j < i) (hj'i : j' < i) (hne : j ≠ j')
    (hwide : c j = c (2 * k + 6 + j')) : False := by
  obtain ⟨h1, -⟩ := crossing hk huaw (a₁ := j) (b₁ := i) (a₂ := 2 * k + 6 + j')
    (b₂ := 2 * k + 6 + i) (by omega) (by omega) (by omega) (by omega) hwide halign
  rw [zw_a (show j < k by omega)] at h1
  rcases (by omega : j' + 1 < k ∨ j' + 1 = k) with h | h
  · rw [zw_a' (by omega) (by omega)] at h1
    simp only [Ltr.a.injEq] at h1; omega
  · rw [zw_d (by omega) (by omega)] at h1; exact absurd h1 (by simp)

/-- **Lemma 5.10(a) (Position constraints, `lem:positions`)**, second half: a non-aligned
wide chord `(j,j')` with `j, j' ≤ k-1` cannot have both indices strictly above an aligned
index `i`. -/
theorem positions_wide_not_above (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    {i j j' : ℕ} (halign : c i = c (2 * k + 6 + i))
    (hij : i < j) (hij' : i < j') (hjk : j < k) (hj'k : j' < k) (hne : j ≠ j')
    (hwide : c j = c (2 * k + 6 + j')) : False := by
  obtain ⟨-, h2⟩ := crossing hk huaw (a₁ := i) (b₁ := j) (a₂ := 2 * k + 6 + i)
    (b₂ := 2 * k + 6 + j') (by omega) (by omega) (by omega) (by omega) halign hwide
  rw [zw_a (show j - 1 < k by omega), show 2 * k + 6 + j' - 1 = 2 * k + 5 + j' by omega] at h2
  rcases (by omega : j' = 0 ∨ 1 ≤ j') with h | h
  · rw [zw_c (by omega)] at h2; exact absurd h2 (by simp)
  · rw [zw_a' (by omega) (by omega)] at h2
    simp only [Ltr.a.injEq] at h2; omega

/-- **Lemma 5.10(b) (Position constraints, `lem:positions`)**: a `PU`-chord `g_j = u`
(`u ∈ {u_1,u_2}`, i.e. `c j = c (3k+6)` or `c j = c (3k+7)`) has `j` below every aligned
index. -/
theorem positions_PU (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    {i j v : ℕ} (halign : c i = c (2 * k + 6 + i))
    (hij : i < j) (hjk : j < k) (hv : v = 3 * k + 6 ∨ v = 3 * k + 7)
    (hchord : c j = c v) : False := by
  obtain ⟨-, h2⟩ := crossing hk huaw (a₁ := i) (b₁ := j) (a₂ := 2 * k + 6 + i)
    (b₂ := v) (by omega) (by omega) (by omega) (by omega) halign hchord
  rw [zw_a (show j - 1 < k by omega)] at h2
  rcases hv with h | h
  · rw [show v - 1 = 3 * k + 5 by omega, zw_d (by omega) rfl] at h2
    exact absurd h2 (by simp)
  · rw [show v - 1 = 3 * k + 6 by omega, zw_e rfl] at h2
    exact absurd h2 (by simp)

/-- **Lemma 5.10(c) (Position constraints, `lem:positions`)**: a `TU`-chord
`h_{j'} = u` has `j'` above every aligned index. -/
theorem positions_TU (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    {i j' v : ℕ} (hik : i < k) (halign : c i = c (2 * k + 6 + i))
    (hj'i : j' < i) (hv : v = 3 * k + 6 ∨ v = 3 * k + 7)
    (hchord : c (2 * k + 6 + j') = c v) : False := by
  obtain ⟨-, h2⟩ := crossing hk huaw (a₁ := i) (b₁ := 2 * k + 6 + j')
    (a₂ := 2 * k + 6 + i) (b₂ := v) (by omega) (by omega) (by omega) (by omega)
    halign hchord
  rw [show 2 * k + 6 + j' - 1 = 2 * k + 5 + j' by omega] at h2
  have hv' : v - 1 = 3 * k + 5 ∨ v - 1 = 3 * k + 6 := by omega
  exact zw_tail_ne hk (x := 2 * k + 5 + j') (y := v - 1) (by omega) (by omega) (by omega) h2

/-- **Lemma 5.10(d) (Position constraints, `lem:positions`)**: a `PP`-chord cannot
straddle an aligned index. -/
theorem positions_PP (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    {i j₁ j₂ : ℕ} (hik : i < k) (halign : c i = c (2 * k + 6 + i))
    (h1 : j₁ < i) (h2 : i < j₂) (hj₂ : j₂ < k) (hchord : c j₁ = c j₂) : False := by
  obtain ⟨hh, -⟩ := crossing hk huaw (a₁ := j₁) (b₁ := i) (a₂ := j₂)
    (b₂ := 2 * k + 6 + i) (by omega) (by omega) (by omega) (by omega) hchord halign
  rw [zw_a (show j₂ < k by omega), zw_a (show j₁ < k by omega)] at hh
  simp only [Ltr.a.injEq] at hh; omega

/-- **Lemma 5.10(d) (Position constraints, `lem:positions`)**: a `TT`-chord cannot
straddle an aligned index. -/
theorem positions_TT (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    {i j₁' j₂' : ℕ} (hik : i < k) (halign : c i = c (2 * k + 6 + i))
    (h1 : j₁' < i) (h2 : i < j₂') (hj₂ : j₂' ≤ k + 1)
    (hchord : c (2 * k + 6 + j₁') = c (2 * k + 6 + j₂')) : False := by
  obtain ⟨-, hl⟩ := crossing hk huaw (a₁ := i) (b₁ := 2 * k + 6 + j₁')
    (a₂ := 2 * k + 6 + i) (b₂ := 2 * k + 6 + j₂') (by omega) (by omega) (by omega)
    (by omega) halign hchord
  rw [show 2 * k + 6 + j₁' - 1 = 2 * k + 5 + j₁' by omega,
    show 2 * k + 6 + j₂' - 1 = 2 * k + 5 + j₂' by omega] at hl
  exact zw_tail_ne hk (x := 2 * k + 5 + j₁') (y := 2 * k + 5 + j₂')
    (by omega) (by omega) (by omega) hl

/-- **Lemma 5.10(e) (Position constraints, `lem:positions`)**: the non-run visit of a
prefix bridge is above every aligned index. -/
theorem positions_prefix_bridge (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    {i j tau : ℕ} (hik : i < k) (halign : c i = c (2 * k + 6 + i))
    (hji : j < i) (htau1 : k ≤ tau) (htau2 : tau ≤ 2 * k + 5)
    (hchord : c j = c tau) : False := by
  obtain ⟨hh, -⟩ := crossing hk huaw (a₁ := j) (b₁ := i) (a₂ := tau)
    (b₂ := 2 * k + 6 + i) (by omega) (by omega) (by omega) (by omega) hchord halign
  rw [zw_a (show j < k by omega)] at hh
  rcases (by omega : tau < 2 * k + 5 ∨ tau = 2 * k + 5) with h | h
  · rw [zw_b (by omega) h] at hh; exact absurd hh (by simp)
  · rw [zw_c h] at hh; exact absurd hh (by simp)

/-- **Lemma 5.10(e) (Position constraints, `lem:positions`)**: the non-run visit of a
tail bridge is below every aligned index. -/
theorem positions_tail_bridge (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    {i j' tau : ℕ} (hik : i < k) (halign : c i = c (2 * k + 6 + i))
    (hij' : i < j') (hj'k : j' < k) (htau1 : k ≤ tau) (htau2 : tau ≤ 2 * k + 5)
    (hchord : c tau = c (2 * k + 6 + j')) : False := by
  obtain ⟨-, hl⟩ := crossing hk huaw (a₁ := i) (b₁ := tau) (a₂ := 2 * k + 6 + i)
    (b₂ := 2 * k + 6 + j') (by omega) (by omega) (by omega) (by omega) halign hchord
  rw [show 2 * k + 6 + j' - 1 = 2 * k + 5 + j' by omega] at hl
  rcases (by omega : tau = k ∨ k < tau) with h | h
  · rw [h, zw_a (show k - 1 < k by omega)] at hl
    rcases (by omega : j' = 0 ∨ 1 ≤ j') with h' | h'
    · rw [h', zw_c (by omega)] at hl; exact absurd hl (by simp)
    · rw [zw_a' (by omega) (by omega)] at hl
      simp only [Ltr.a.injEq] at hl; omega
  · rw [zw_b (by omega) (by omega)] at hl
    rcases (by omega : j' = 0 ∨ 1 ≤ j') with h' | h'
    · rw [h', zw_c (by omega)] at hl; exact absurd hl (by simp)
    · rw [zw_a' (by omega) (by omega)] at hl; exact absurd hl (by simp)

/-- **Lemma 5.10(e) (Position constraints, `lem:positions`)**: neither `u_1` nor `u_2`
is a bridge. -/
theorem positions_u_not_bridge (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    {i tau v : ℕ} (hik : i < k) (halign : c i = c (2 * k + 6 + i))
    (htau1 : k ≤ tau) (htau2 : tau ≤ 2 * k + 5) (hv : v = 3 * k + 6 ∨ v = 3 * k + 7)
    (hchord : c tau = c v) : False := by
  obtain ⟨-, hl⟩ := crossing hk huaw (a₁ := i) (b₁ := tau) (a₂ := 2 * k + 6 + i)
    (b₂ := v) (by omega) (by omega) (by omega) (by omega) halign hchord
  have hlet : zw k (tau - 1) = Ltr.a k ∨ zw k (tau - 1) = Ltr.b := by
    rcases (by omega : tau = k ∨ k < tau) with h | h
    · left; rw [h, zw_a (show k - 1 < k by omega)]; congr 1; omega
    · right; exact zw_b (by omega) (by omega)
  rcases hv with h | h
  · rw [show v - 1 = 3 * k + 5 by omega, zw_d (by omega) rfl] at hl
    rcases hlet with h' | h' <;> rw [h'] at hl <;> exact absurd hl (by simp)
  · rw [show v - 1 = 3 * k + 6 by omega, zw_e rfl] at hl
    rcases hlet with h' | h' <;> rw [h'] at hl <;> exact absurd hl (by simp)

/-- **Lemma 5.10(f) (Position constraints, `lem:positions`)**: `u_1 ≠ u_2`.  Indeed
`u_1 = u_2` would be a narrow tail chord of length `1`, excluded by Lemma 5.6(b)
(`lem:narrow`) with `σ = ℓ`. -/
theorem positions_u1_ne_u2 (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) (h : c (3 * k + 6) = c (3 * k + 7)) : False := by
  refine narrow_tail_insert hk huaw Str (i := 3 * k + 6) (j := 3 * k + 7) (σ := Str.ell)
    (by omega) (by omega) (by omega) h Str.hell ?_ ?_
  · rw [show 3 * k + 7 - (3 * k + 6) = 1 by omega, Nat.mul_one]
  · rw [show 3 * k + 7 - (3 * k + 6) = 1 by omega, Nat.mul_one]
    exact Nat.le_mul_of_pos_left _ Str.htt

/-- **Lemma 5.10(f) (Position constraints, `lem:positions`)**: if `g_j = u_1` then `u_2`
is not a tail state `h_{j'}`. -/
theorem positions_PU_TU_incompatible (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    {j j' : ℕ} (hjk : j < k) (hj'k : j' < k)
    (h1 : c j = c (3 * k + 6)) (h2 : c (2 * k + 6 + j') = c (3 * k + 7)) : False := by
  obtain ⟨hh, -⟩ := crossing hk huaw (a₁ := j) (b₁ := 2 * k + 6 + j') (a₂ := 3 * k + 6)
    (b₂ := 3 * k + 7) (by omega) (by omega) (by omega) (by omega) h1 h2
  rw [zw_e rfl, zw_a (show j < k by omega)] at hh
  exact absurd hh (by simp)

end

end AneVsAn
