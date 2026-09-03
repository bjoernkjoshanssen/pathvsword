import RequestProject.WalkSurgery

/-!
# Two further surgeries (Sections 5.3 and 6.4 of `ane-vs-an-separation-v4_1.tex`)

This file supplements `RequestProject/WalkSurgery.lean` with the two surgeries that the
endgame of Section 6 needs and that were not required earlier:

* `narrow_pair_sum` — **Lemma 5.6(d) (`lem:narrow`)**: the *double insertion*
  `W[0,j] W[i,j'] W[i',n]` of two narrow chords `(i,j)` and `(i',j')`, which has length
  `n + λ + λ'` and is corrected by `R⟨m-λ-λ'⟩`;
* `pu_swap` — the path `π = W[0,j₁] · e_{3k+6} · W[j₂,n]` of the second assertion of
  Lemma 6.6(c) (`lem:parity2`): if `g_{j₁} = u₁` and `g_{j₂} = u₂` with `j₂ < j₁`, the
  `e`-edge `(u₁,e,u₂)` lets the path jump from `g_{j₁}` back to `g_{j₂}`.
-/

namespace AneVsAn

set_option autoImplicit false

section

variable {k : ℕ} {S : Type} {c : ℕ → S}

/-- **Lemma 5.6(d) (Narrow surgeries, `lem:narrow`)**: two narrow chords `(i₁,j₁)` and
`(i₂,j₂)` (listed so that `i₁ < i₂`) whose lengths add up to a multiple of `ℓ` that is at
most `tℓ` are excluded.  The path is the double insertion `W[0,j₁] W[i₁,j₂] W[i₂,n]`, of
length `n + λ₁ + λ₂`, with the run replaced by `R⟨m - λ₁ - λ₂⟩`. -/
theorem narrow_pair_sum (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c)
    {i₁ j₁ i₂ j₂ : ℕ} (h1 : i₁ < j₁) (h2 : i₂ < j₂) (h12 : i₁ < i₂)
    (hn1 : j₁ < k ∨ (2 * k + 6 ≤ i₁ ∧ j₁ ≤ 3 * k + 7))
    (hn2 : j₂ < k ∨ (2 * k + 6 ≤ i₂ ∧ j₂ ≤ 3 * k + 7))
    (e1 : c i₁ = c j₁) (e2 : c i₂ = c j₂)
    (hdvd : Str.ell ∣ ((j₁ - i₁) + (j₂ - i₂)))
    (hle : (j₁ - i₁) + (j₂ - i₂) ≤ Str.tt * Str.ell) : False := by
  have hd0 := Str.d0_add
  have hell := Str.hell
  obtain ⟨u₀, hu₀⟩ := hdvd
  have hu₀' : (j₁ - i₁) + (j₂ - i₂) = u₀ * Str.ell := by rw [hu₀]; ring
  have hmul : u₀ * Str.ell ≤ Str.tt * Str.ell := by omega
  have key : Str.d0 + (Str.tt - u₀) * Str.ell + ((j₁ - i₁) + (j₂ - i₂)) = k + 5 := by
    rw [Nat.sub_mul]; omega
  rcases hn1 with hp1 | ht1
  · rcases hn2 with hp2 | ht2
    · -- both chords on the prefix side
      exact narrow_prefix_pair hk huaw Str (a₁ := i₁) (a₂ := j₁) (x := j₂) (y := i₂)
        (u := Str.tt - u₀) (by omega) h1 hp1 (by omega) (by omega) e1 e2.symm (by omega)
    · -- the first chord on the prefix side, the second on the tail side
      exact narrow_mixed_pair hk huaw Str (a₁ := i₁) (a₂ := j₁) (x := j₂) (y := i₂)
        (u := Str.tt - u₀) h1 hp1 (by omega) (by omega) (by omega) e1 e2.symm (by omega)
  · -- both chords on the tail side
    have ht2 : 2 * k + 6 ≤ i₂ ∧ j₂ ≤ 3 * k + 7 := by
      rcases hn2 with h' | h'
      · omega
      · exact h'
    exact narrow_tail_pair hk huaw Str (a₁ := i₁) (a₂ := j₁) (x := j₂) (y := i₂)
      (u := Str.tt - u₀) ht1.1 h1 ht1.2 (by omega) (by omega) (by omega) e1 e2.symm
      (by omega) (by omega)

/-- **Lemma 6.6(c) (`lem:parity2`), second assertion**: if `g_{j₁} = u₁` and
`g_{j₂} = u₂` are two `PU`-chords with `j₂ < j₁`, then the path
`π = W[0,j₁] · e_{3k+6} · W[j₂,n]`, with the run inside `W[j₂,n]` replaced by
`R⟨m - (j₁+1-j₂)⟩`, is a second accepting path of length `n` as soon as
`ℓ ∣ j₁+1-j₂` and `j₁+1-j₂ ≤ tℓ`.  (It reads `e` at position `j₁`, where `W` reads
`a_{j₁+1}`.) -/
theorem pu_swap (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) {j₁ j₂ : ℕ} (h21 : j₂ < j₁) (hj₁ : j₁ < k)
    (hu1 : c j₁ = c (3 * k + 6)) (hu2 : c j₂ = c (3 * k + 7))
    (hdvd : Str.ell ∣ (j₁ + 1 - j₂)) (hle : j₁ + 1 - j₂ ≤ Str.tt * Str.ell) : False := by
  obtain ⟨u₀, hu₀⟩ := hdvd
  have hu₀' : j₁ + 1 - j₂ = u₀ * Str.ell := by rw [hu₀]; ring
  clear hu₀
  have hrun : Str.d0 + (Str.tt - u₀) * Str.ell + (j₁ + 1 - j₂) = k + 5 := by
    have hA := Str.d0_add
    have hB : u₀ * Str.ell ≤ Str.tt * Str.ell := by omega
    rw [Nat.sub_mul]
    omega
  obtain ⟨τr, hτr⟩ := Str.runSeg hk (Str.tt - u₀)
  have p1 : Seg k c (c 0) (c j₁) j₁ (fun t => 0 + t) := by
    have h := segW (k := k) c (show (0 : ℕ) ≤ j₁ by omega) (by omega)
    simpa using h
  rw [hu1] at p1
  have p2 : Seg k c (c (3 * k + 6)) (c (3 * k + 7)) 1 (fun t => 3 * k + 6 + t) := by
    have h := segW (k := k) c (show 3 * k + 6 ≤ 3 * k + 7 by omega) (by omega)
    rw [show 3 * k + 7 - (3 * k + 6) = 1 by omega] at h
    exact h
  rw [← hu2] at p2
  have p3 : Seg k c (c j₂) (c k) (k - j₂) (fun t => j₂ + t) := segW c (by omega) (by omega)
  have p4 : Seg k c (c (2 * k + 5)) (c (3 * k + 7)) (k + 2) (fun t => 2 * k + 5 + t) := by
    have h := segW (k := k) c (show 2 * k + 5 ≤ 3 * k + 7 by omega) (by omega)
    rw [show 3 * k + 7 - (2 * k + 5) = k + 2 by omega] at h; exact h
  have hall := seg_cat p1 (seg_cat p2 (seg_cat p3 (seg_cat hτr p4)))
  have hL : j₁ + (1 + (k - j₂ + (Str.d0 + (Str.tt - u₀) * Str.ell + (k + 2))))
      = 3 * k + 7 := by omega
  rw [hL] at hall
  refine no_second_path hk huaw hall (j := j₁) (by omega) ?_
  have hτj : cat j₁ (fun t => 0 + t)
      (cat 1 (fun t => 3 * k + 6 + t)
        (cat (k - j₂) (fun t => j₂ + t)
          (cat (Str.d0 + (Str.tt - u₀) * Str.ell) τr (fun t => 2 * k + 5 + t))))
        j₁ = 3 * k + 6 := by
    rw [cat_ge (by omega), Nat.sub_self, cat_lt (by omega)]
  rw [hτj, zw_e rfl, zw_a hj₁]
  simp

end

end AneVsAn
