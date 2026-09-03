import RequestProject.WalkEll4

/-!
# Cluster states off the cycle `γ` (Steps 2, 4 and 5 of Lemma 5.3, `lem:gamma`)

This file formalizes the part of Lemma 5.3 (`lem:gamma`) of `anevsanseparationv4.tex`
that is not covered by Step 1 (the existence of the cycle `γ` and of a maximal stretch
`S`, carried out in `RequestProject/WalkGamma.lean` and in `exists_maximal_Stretch`):

* Step 2 (*no second cycle*): a cluster state off `γ` is visited at most twice;
* Step 5 (*no exceptional states*): in fact it is visited exactly once, i.e. `x_e = 0`;
* Step 4: the resulting bound `d₀ ≤ 6`, in the bookkeeping form `eq:dzero`.

The engine is a family of *loop surgeries*.  If `y` is a state with two visits at run
times `v` and `v+L` outside the stretch, then `W[v,v+L]` is a closed `b`-labelled walk
`κ` at `y`, and a second accepting path of length `n` is obtained by traversing `κ` a
different number of times and compensating the length by *spin adjustment*, i.e. by going
a different number of times around `γ` (Section 5.2 of `anevsanseparationv4.tex`).  The
four possible positions of `κ` relative to the stretch give the four surgeries
`loop_insert_left`, `loop_skip_left`, `loop_insert_right`, `loop_skip_right`; the case in
which the two visits lie on opposite sides of the stretch gives `loop_span`.
-/

namespace AneVsAn

set_option autoImplicit false

section

variable {k : ℕ} {S : Type} {c : ℕ → S}

/-- The paths `R_x^y⟨t'⟩` of Lemma 5.3(iii) (`lem:gamma`) together with the explicit
description of their itinerary: they walk from `x` to `p = k+α`, then go `u` times around
`γ`, then follow the walk from `p` for `r_off` steps (arriving at `c_q`) and finally
follow the walk from `q = 2k+5-ω` to `y`.  This refinement of `Stretch.spanSeg` is what
makes it possible to read off the state of the path at a prescribed position. -/
theorem spanSegI (Str : Stretch k c) {x y : ℕ} (hx : x ≤ Str.p) (hy : Str.q ≤ y)
    (hyn : y ≤ 3 * k + 7) (u : ℕ) :
    ∃ τ, Seg k c (c x) (c y) (Str.slen x y u) τ ∧
      (∀ j, j < Str.p - x → τ j = x + j) ∧
      (1 ≤ u * Str.ell + Str.roff → τ (Str.p - x) = Str.p) ∧
      (∀ j, j < y - Str.q →
        τ ((Str.p - x) + (u * Str.ell + Str.roff) + j) = Str.q + j) := by
  have hell := Str.hell
  have htt := Str.htt
  have hlenS := Str.hlen
  have hmul : Str.ell ≤ Str.tt * Str.ell := Nat.le_mul_of_pos_left _ htt
  have hpq : Str.p + Str.ell ≤ Str.q := by omega
  have hqn : Str.q ≤ 3 * k + 7 := by omega
  have hloopEnd : c (Str.p + Str.ell) = c Str.p := (Str.hper Str.p le_rfl (by omega)).symm
  have hloop : Seg k c (c Str.p) (c Str.p) Str.ell (fun t => Str.p + t) := by
    have h := segW (k := k) c (show Str.p ≤ Str.p + Str.ell by omega) (by omega)
    rw [hloopEnd, show Str.p + Str.ell - Str.p = Str.ell by omega] at h
    exact h
  have hroffEnd : c (Str.p + Str.roff) = c Str.q := by
    have h := period_iter Str.hper Str.tt (Str.p + Str.roff) (by omega) (by omega)
    rw [show Str.p + Str.roff + Str.tt * Str.ell = Str.q by omega] at h
    exact h
  have hleft : Seg k c (c x) (c Str.p) (Str.p - x) (fun t => x + t) := segW c hx (by omega)
  have hmid : Seg k c (c Str.p) (c Str.p) (u * Str.ell) (repit u Str.ell (fun t => Str.p + t)) :=
    seg_repit hloop u
  have hoff : Seg k c (c Str.p) (c Str.q) Str.roff (fun t => Str.p + t) := by
    have h := segW (k := k) c (show Str.p ≤ Str.p + Str.roff by omega) (by omega)
    rw [hroffEnd, show Str.p + Str.roff - Str.p = Str.roff by omega] at h
    exact h
  have hright : Seg k c (c Str.q) (c y) (y - Str.q) (fun t => Str.q + t) := segW c hy hyn
  have hall := seg_cat hleft (seg_cat hmid (seg_cat hoff hright))
  rw [show Str.p - x + (u * Str.ell + (Str.roff + (y - Str.q))) = Str.slen x y u by
    simp only [Stretch.slen]; omega] at hall
  refine ⟨_, hall, ?_, ?_, ?_⟩
  · intro j hj
    rw [cat_lt hj]
  · intro hu
    rw [cat_ge (by omega), Nat.sub_self]
    rcases Nat.eq_zero_or_pos (u * Str.ell) with h0 | h0
    · have hroff : 1 ≤ Str.roff := by omega
      rw [cat_ge (by omega), show (0 : ℕ) - u * Str.ell = 0 by omega, cat_lt (by omega)]
      simp
    · have hu1 : 1 ≤ u := by
        rcases Nat.eq_zero_or_pos u with rfl | h
        · simp at h0
        · exact h
      rw [cat_lt h0, repit_zero hu1 hell]
      simp
  · intro j hj
    rw [cat_ge (by omega),
      show Str.p - x + (u * Str.ell + Str.roff) + j - (Str.p - x)
        = u * Str.ell + (Str.roff + j) by omega,
      cat_ge (by omega), show u * Str.ell + (Str.roff + j) - u * Str.ell = Str.roff + j by omega,
      cat_ge (by omega), show Str.roff + j - Str.roff = j by omega]

/-- Every time of the stretch `S = [p,q]` visits a state of the cycle `γ`: this is
Lemma 5.3(i) (`lem:gamma`), "on `S` the walk follows `γ`". -/
theorem stretch_state (Str : Stretch k c) {u : ℕ} (hpu : Str.p ≤ u) (huq : u ≤ Str.q) :
    ∃ x, Str.p ≤ x ∧ x < Str.p + Str.ell ∧ c x = c u := by
  have hell := Str.hell
  refine ⟨Str.p + (u - Str.p) % Str.ell, by omega, by
    have := Nat.mod_lt (u - Str.p) (show 0 < Str.ell by omega); omega, ?_⟩
  have hdm : (u - Str.p) % Str.ell + (u - Str.p) / Str.ell * Str.ell = u - Str.p := by
    have h := Nat.div_add_mod (u - Str.p) Str.ell
    rw [Nat.mul_comm] at h
    omega
  have h := period_iter Str.hper ((u - Str.p) / Str.ell) (Str.p + (u - Str.p) % Str.ell)
    (by omega) (by omega)
  rw [show Str.p + (u - Str.p) % Str.ell + (u - Str.p) / Str.ell * Str.ell = u by omega] at h
  exact h

/-!
### The loop surgeries of Step 5 of Lemma 5.3 (`lem:gamma`)

In each of the following five lemmas `y` is a state visited at two run times, and
`κ = W[v, v+L]` (or, in `loop_span`, the walk between the two visits) is the resulting
closed `b`-labelled walk at `y`.  The second accepting path traverses `κ` a different
number of times and compensates the length by *spin adjustment*.  The hypothesis `hmax`
is the maximality of the stretch (Step 1 of Lemma 5.3): every visit of a `γ`-state is a
time of `S`.
-/

/-- **Step 5 of Lemma 5.3 (`lem:gamma`)**, loop before the stretch, inserted.  If the
loop `κ = W[v,v+L]` lies before the stretch and `J·L + σ·ℓ = t·ℓ`, the path
`W[0,v] κ^J R_v^n⟨σ turns⟩` has length `n`; it enters the stretch `J·L` steps late, so at
the position `p + J·L - 1` it carries a state visited before `p`, whereas `W` carries a
`γ`-state there — contradicting the maximality of the stretch. -/
theorem loop_insert_left (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c)
    (hmax : ∀ u, u ≤ 3 * k + 7 → (∃ x, Str.p ≤ x ∧ x < Str.p + Str.ell ∧ c x = c u) →
      Str.p ≤ u ∧ u ≤ Str.q)
    {v L J sig : ℕ} (hL : 1 ≤ L) (hvL : v + L ≤ Str.p) (heq : c v = c (v + L))
    (hJ : 1 ≤ J) (hlen : J * L + sig * Str.ell = Str.tt * Str.ell) : False := by
  have hp := Str.hp
  have hq := Str.hq
  have hlenS := Str.hlen
  have hJL : 1 ≤ J * L := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hJLle : J * L ≤ Str.tt * Str.ell := by omega
  have s0 : Seg k c (c 0) (c v) v (fun t => 0 + t) := by
    have h := segW (k := k) c (show (0 : ℕ) ≤ v by omega) (by omega)
    simpa using h
  have hloop : Seg k c (c v) (c v) L (fun t => v + t) := by
    have h := segW (k := k) c (show v ≤ v + L by omega) (by omega)
    rw [← heq, show v + L - v = L by omega] at h
    exact h
  have hJloop := seg_repit hloop J
  obtain ⟨τs, hspan, hinit, -, -⟩ :=
    spanSegI Str (x := v) (y := 3 * k + 7) (by omega) (by omega) le_rfl sig
  have hall := seg_cat s0 (seg_cat hJloop hspan)
  rw [show v + (J * L + Str.slen v (3 * k + 7) sig) = 3 * k + 7 by
    simp only [Stretch.slen]; omega] at hall
  set j := Str.p + J * L - 1 with hj
  have hτ : cat v (fun t => 0 + t) (cat (J * L) (repit J L (fun t => v + t)) τs) j
      = Str.p - 1 := by
    rw [cat_ge (by omega), cat_ge (by omega), hinit (j - v - J * L) (by omega)]
    omega
  have hst := (pathTo_spec hk huaw hall).2 j (by omega)
  rw [hτ] at hst
  obtain ⟨x, hx1, hx2, hx3⟩ := stretch_state Str (u := j) (by omega) (by omega)
  have := (hmax (Str.p - 1) (by omega) ⟨x, hx1, hx2, by rw [hx3, ← hst]⟩).1
  omega

/-- **Step 5 of Lemma 5.3 (`lem:gamma`)**, loop before the stretch, skipped.  If
`σ·ℓ = L + t·ℓ`, the path `W[0,v] R_{v+L}^n⟨σ turns⟩` skips the loop and adds `L/ℓ` turns;
it enters the stretch `L` steps early, so the state `c_p` of `γ` is visited at the time
`p - L` outside the stretch, contradicting its maximality. -/
theorem loop_skip_left (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c)
    (hmax : ∀ u, u ≤ 3 * k + 7 → (∃ x, Str.p ≤ x ∧ x < Str.p + Str.ell ∧ c x = c u) →
      Str.p ≤ u ∧ u ≤ Str.q)
    {v L sig : ℕ} (hL : 1 ≤ L) (hvL : v + L ≤ Str.p) (heq : c v = c (v + L))
    (hlen : sig * Str.ell = L + Str.tt * Str.ell) : False := by
  have hp := Str.hp
  have hq := Str.hq
  have hlenS := Str.hlen
  have s0 : Seg k c (c 0) (c v) v (fun t => 0 + t) := by
    have h := segW (k := k) c (show (0 : ℕ) ≤ v by omega) (by omega)
    simpa using h
  obtain ⟨τs, hspan, -, hmidp, -⟩ :=
    spanSegI Str (x := v + L) (y := 3 * k + 7) (by omega) (by omega) le_rfl sig
  rw [← heq] at hspan
  have hall := seg_cat s0 hspan
  rw [show v + Str.slen (v + L) (3 * k + 7) sig = 3 * k + 7 by
    simp only [Stretch.slen]; omega] at hall
  have hτ : cat v (fun t => 0 + t) τs (Str.p - L) = Str.p := by
    rw [cat_ge (by omega), show Str.p - L - v = Str.p - (v + L) by omega,
      hmidp (by omega)]
  have hst := (pathTo_spec hk huaw hall).2 (Str.p - L) (by omega)
  rw [hτ] at hst
  have := (hmax (Str.p - L) (by omega) ⟨Str.p, le_rfl, by have := Str.hell; omega, hst⟩).1
  omega

/-- **Step 5 of Lemma 5.3 (`lem:gamma`)**, loop after the stretch, inserted.  The path
`R_0^v⟨σ turns⟩ κ^J W[v,n]` leaves the stretch `J·L` steps early, so the state `c_{q+1}`,
which is visited outside the stretch, would be a `γ`-state. -/
theorem loop_insert_right (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c)
    (hmax : ∀ u, u ≤ 3 * k + 7 → (∃ x, Str.p ≤ x ∧ x < Str.p + Str.ell ∧ c x = c u) →
      Str.p ≤ u ∧ u ≤ Str.q)
    {v L J sig : ℕ} (hL : 1 ≤ L) (hqv : Str.q < v) (hvL : v + L ≤ 3 * k + 7)
    (heq : c v = c (v + L)) (hJ : 1 ≤ J)
    (hlen : J * L + sig * Str.ell = Str.tt * Str.ell) : False := by
  have hp := Str.hp
  have hq := Str.hq
  have hlenS := Str.hlen
  have hJL : 1 ≤ J * L := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  obtain ⟨τs, hspan, -, -, htail⟩ :=
    spanSegI Str (x := 0) (y := v) (by omega) (by omega) (by omega) sig
  have hloop : Seg k c (c v) (c v) L (fun t => v + t) := by
    have h := segW (k := k) c (show v ≤ v + L by omega) (by omega)
    rw [← heq, show v + L - v = L by omega] at h
    exact h
  have hJloop := seg_repit hloop J
  have hend : Seg k c (c v) (c (3 * k + 7)) (3 * k + 7 - v) (fun t => v + t) :=
    segW c (by omega) (by omega)
  have hall := seg_cat hspan (seg_cat hJloop hend)
  rw [show Str.slen 0 v sig + (J * L + (3 * k + 7 - v)) = 3 * k + 7 by
    simp only [Stretch.slen]; omega] at hall
  set j := Str.p + (sig * Str.ell + Str.roff) + 1 with hjdef
  have hslen : Str.slen 0 v sig = Str.p + (sig * Str.ell + Str.roff) + (v - Str.q) := by
    simp only [Stretch.slen]; omega
  have hτ : cat (Str.slen 0 v sig) τs
      (cat (J * L) (repit J L (fun t => v + t)) (fun t => v + t)) j = Str.q + 1 := by
    rcases (by omega : Str.q + 1 < v ∨ v = Str.q + 1) with hcase | hcase
    · rw [cat_lt (by omega)]
      have := htail 1 (by omega)
      simpa using this
    · rw [cat_ge (by omega), show j - Str.slen 0 v sig = 0 by omega, cat_lt (by omega),
        repit_zero hJ hL]
      omega
  have hst := (pathTo_spec hk huaw hall).2 j (by omega)
  rw [hτ] at hst
  obtain ⟨x, hx1, hx2, hx3⟩ := stretch_state Str (u := j) (by omega) (by omega)
  have := (hmax (Str.q + 1) (by omega) ⟨x, hx1, hx2, by rw [hx3, ← hst]⟩).2
  omega

/-- **Step 5 of Lemma 5.3 (`lem:gamma`)**, loop after the stretch, skipped.  The path
`R_0^v⟨σ turns⟩ W[v+L,n]` skips the loop and adds `L/ℓ` turns, so it leaves the stretch
`L` steps late: the `γ`-state `c_q` would be visited at the time `q + L`. -/
theorem loop_skip_right (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c)
    (hmax : ∀ u, u ≤ 3 * k + 7 → (∃ x, Str.p ≤ x ∧ x < Str.p + Str.ell ∧ c x = c u) →
      Str.p ≤ u ∧ u ≤ Str.q)
    {v L sig : ℕ} (hL : 1 ≤ L) (hqv : Str.q < v) (hvL : v + L ≤ 3 * k + 7)
    (heq : c v = c (v + L)) (hlen : sig * Str.ell = L + Str.tt * Str.ell) : False := by
  have hp := Str.hp
  have hq := Str.hq
  have hlenS := Str.hlen
  obtain ⟨τs, hspan, -, -, htail⟩ :=
    spanSegI Str (x := 0) (y := v) (by omega) (by omega) (by omega) sig
  have hend : Seg k c (c v) (c (3 * k + 7)) (3 * k + 7 - (v + L)) (fun t => v + L + t) := by
    have h := segW (k := k) c (show v + L ≤ 3 * k + 7 by omega) (by omega)
    rw [← heq] at h
    exact h
  have hall := seg_cat hspan hend
  rw [show Str.slen 0 v sig + (3 * k + 7 - (v + L)) = 3 * k + 7 by
    simp only [Stretch.slen]; omega] at hall
  set j := Str.p + (sig * Str.ell + Str.roff) with hjdef
  have hslen : Str.slen 0 v sig = Str.p + (sig * Str.ell + Str.roff) + (v - Str.q) := by
    simp only [Stretch.slen]; omega
  have hτ : cat (Str.slen 0 v sig) τs (fun t => v + L + t) j = Str.q := by
    rw [cat_lt (by omega)]
    have := htail 0 (by omega)
    simpa using this
  have hst := (pathTo_spec hk huaw hall).2 j (by omega)
  rw [hτ] at hst
  obtain ⟨x, hx1, hx2, hx3⟩ := stretch_state Str (u := Str.q) (by omega) le_rfl
  have hjq : j = Str.q + L := by omega
  rw [hjq] at hst
  have := (hmax (Str.q + L) (by omega) ⟨x, hx1, hx2, by rw [hx3, hst]⟩).2
  omega

/-- **Step 5 of Lemma 5.3 (`lem:gamma`)**, the two visits on opposite sides of the
stretch.  Here the closed walk `κ = W[v₁,v₂]` contains the stretch, and traversing it
`J+1` times with a total of `σ` turns around `γ` gives a path of length `n`; at the end
of the first traversal it carries the state `y = c_{v₁}` at the position `v₁ + ε`, where
`ε = L - tℓ`. -/
theorem loop_span (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c) (Str : Stretch k c)
    {v₁ v₂ J sig : ℕ} (hv₁ : v₁ < Str.p) (hqv₂ : Str.q < v₂) (hv₂ : v₂ ≤ 3 * k + 7)
    (heq : c v₁ = c v₂) (hJ : 1 ≤ J)
    (hlen : J * Str.slen v₁ v₂ 0 + sig * Str.ell = Str.tt * Str.ell)
    (hne : c (v₁ + Str.slen v₁ v₂ 0) ≠ c v₁) : False := by
  have hp := Str.hp
  have hq := Str.hq
  have hlenS := Str.hlen
  set eps := Str.slen v₁ v₂ 0 with heps
  have hepsval : eps = (Str.p - v₁) + Str.roff + (v₂ - Str.q) := by
    simp only [heps, Stretch.slen]; omega
  have heps2 : 2 ≤ eps := by omega
  have hepsJ : eps ≤ J * eps := Nat.le_mul_of_pos_left _ hJ
  have s0 : Seg k c (c 0) (c v₁) v₁ (fun t => 0 + t) := by
    have h := segW (k := k) c (show (0 : ℕ) ≤ v₁ by omega) (by omega)
    simpa using h
  obtain ⟨τ0, hseg0, hinit0, -, -⟩ :=
    spanSegI Str (x := v₁) (y := v₂) (by omega) (by omega) (by omega) 0
  rw [← heq] at hseg0
  have hJ0 := seg_repit hseg0 J
  obtain ⟨τs, hsegs, hinits, -, -⟩ :=
    spanSegI Str (x := v₁) (y := v₂) (by omega) (by omega) (by omega) sig
  have hend : Seg k c (c v₂) (c (3 * k + 7)) (3 * k + 7 - v₂) (fun t => v₂ + t) :=
    segW c (by omega) (by omega)
  have hslensig : Str.slen v₁ v₂ sig = eps + sig * Str.ell := by
    simp only [heps, Stretch.slen]; omega
  have hall := seg_cat s0 (seg_cat hJ0 (seg_cat hsegs hend))
  rw [show v₁ + (J * eps + (Str.slen v₁ v₂ sig + (3 * k + 7 - v₂))) = 3 * k + 7 by
    rw [hslensig]; omega] at hall
  have hτ : cat v₁ (fun t => 0 + t)
      (cat (J * eps) (repit J eps τ0)
        (cat (Str.slen v₁ v₂ sig) τs (fun t => v₂ + t))) (v₁ + eps) = v₁ := by
    rw [cat_ge (by omega), show v₁ + eps - v₁ = eps by omega]
    rcases (by omega : 2 ≤ J ∨ J = 1) with hcase | hcase
    · rw [cat_lt (by
        have : 2 * eps ≤ J * eps := Nat.mul_le_mul_right _ hcase
        omega)]
      obtain ⟨J', rfl⟩ : ∃ J', J = J' + 1 := ⟨J - 1, by omega⟩
      rw [repit_at_period, repit_zero (by omega) (by omega)]
      exact hinit0 0 (by omega)
    · subst hcase
      rw [cat_ge (by omega), show eps - 1 * eps = 0 by omega, cat_lt (by omega)]
      exact hinits 0 (by omega)
  have hst := (pathTo_spec hk huaw hall).2 (v₁ + eps) (by omega)
  rw [hτ] at hst
  exact hne hst.symm

/-- The *spin adjustment* arithmetic of Section 5.2 of `anevsanseparationv4.tex`: if a
loop of length `L ≤ t` is to be traversed `J` extra times, the compensating number `σ` of
turns around `γ` exists.  With `g = gcd(L,ℓ)` one takes `J = ℓ/g` and `σ = t - L/g`. -/
theorem exists_spin {ell L tt : ℕ} (hell : 1 ≤ ell) (hL : 1 ≤ L) (hLt : L ≤ tt) :
    ∃ J sig, 1 ≤ J ∧ J * L + sig * ell = tt * ell := by
  set g := Nat.gcd L ell with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
  obtain ⟨a, ha⟩ : g ∣ L := Nat.gcd_dvd_left _ _
  obtain ⟨b, hb⟩ : g ∣ ell := Nat.gcd_dvd_right _ _
  have hb1 : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with rfl | h
    · simp at hb; omega
    · exact h
  have hat : a ≤ tt := by
    have : a ≤ L := by
      calc a = 1 * a := (one_mul a).symm
        _ ≤ g * a := Nat.mul_le_mul_right _ hgpos
        _ = L := ha.symm
    omega
  refine ⟨b, tt - a, hb1, ?_⟩
  have h1 : b * L = a * ell := by rw [ha, hb]; ring
  rw [h1, ← Nat.add_mul, show a + (tt - a) = tt by omega]

/-- **Steps 2 and 5 of Lemma 5.3 (`lem:gamma`)**, loops before the stretch.  A closed
walk `W[v,v+L]` lying entirely before the stretch is impossible as soon as `L ≤ t` or
`ℓ ∣ L`. -/
theorem loop_left_false (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c)
    (hmax : ∀ u, u ≤ 3 * k + 7 → (∃ x, Str.p ≤ x ∧ x < Str.p + Str.ell ∧ c x = c u) →
      Str.p ≤ u ∧ u ≤ Str.q)
    {v L : ℕ} (hL : 1 ≤ L) (hvL : v + L ≤ Str.p) (heq : c v = c (v + L))
    (hcase : L ≤ Str.tt ∨ Str.ell ∣ L) : False := by
  rcases hcase with hLt | ⟨w, hw⟩
  · obtain ⟨J, sig, hJ, hlen⟩ := exists_spin (ell := Str.ell) Str.hell hL hLt
    exact loop_insert_left hk huaw Str hmax hL hvL heq hJ hlen
  · refine loop_skip_left hk huaw Str hmax hL hvL heq (sig := Str.tt + w) ?_
    rw [hw]; ring

/-- **Steps 2 and 5 of Lemma 5.3 (`lem:gamma`)**, loops after the stretch. -/
theorem loop_right_false (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c)
    (hmax : ∀ u, u ≤ 3 * k + 7 → (∃ x, Str.p ≤ x ∧ x < Str.p + Str.ell ∧ c x = c u) →
      Str.p ≤ u ∧ u ≤ Str.q)
    {v L : ℕ} (hL : 1 ≤ L) (hqv : Str.q < v) (hvL : v + L ≤ 3 * k + 7)
    (heq : c v = c (v + L)) (hcase : L ≤ Str.tt ∨ Str.ell ∣ L) : False := by
  rcases hcase with hLt | ⟨w, hw⟩
  · obtain ⟨J, sig, hJ, hlen⟩ := exists_spin (ell := Str.ell) Str.hell hL hLt
    exact loop_insert_right hk huaw Str hmax hL hqv hvL heq hJ hlen
  · refine loop_skip_right hk huaw Str hmax hL hqv hvL heq (sig := Str.tt + w) ?_
    rw [hw]; ring

/-- **Step 5 of Lemma 5.3 (`lem:gamma`)**, two visits on opposite sides of the stretch:
the surgery applies as soon as `ε = L - tℓ ≤ t` and the position `v₁ + ε` is not a visit
of `y`. -/
theorem loop_span_false (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (Str : Stretch k c) {v₁ v₂ : ℕ} (hv₁ : v₁ < Str.p) (hqv₂ : Str.q < v₂)
    (hv₂ : v₂ ≤ 3 * k + 7) (heq : c v₁ = c v₂) (hle : Str.slen v₁ v₂ 0 ≤ Str.tt)
    (hne : c (v₁ + Str.slen v₁ v₂ 0) ≠ c v₁) : False := by
  have hpos : 1 ≤ Str.slen v₁ v₂ 0 := by simp only [Stretch.slen]; omega
  obtain ⟨J, sig, hJ, hlen⟩ := exists_spin (ell := Str.ell) Str.hell hpos hle
  exact loop_span hk huaw Str hv₁ hqv₂ hv₂ heq hJ hlen hne

end

section

variable {k : ℕ} {S : Type} [DecidableEq S] {c : ℕ → S}

/-- The cluster states that do **not** lie on the cycle `γ` of Lemma 5.3 (`lem:gamma`).
The states of `γ` are the states `c x` for `x` in one period `[p, p+ℓ)` of the stretch. -/
def offCycle (Str : Stretch k c) : Finset S :=
  (cluster k c).filter (fun s => ∀ x ∈ Finset.Ico Str.p (Str.p + Str.ell), c x ≠ s)

/-- The number `x₁` of Lemma 5.3(ii) (`lem:gamma`): the number of cluster states off `γ`.
By Lemma 5.3(v) (`x_e = 0`) each of them is visited exactly once. -/
def offCycleCard (Str : Stretch k c) : ℕ := (offCycle Str).card

/-- The states of the cycle `γ` of Lemma 5.3 (`lem:gamma`): the states carried by one
period `[p, p+ℓ)` of the stretch. -/
def gammaSet (Str : Stretch k c) : Finset S :=
  (Finset.Ico Str.p (Str.p + Str.ell)).image c

theorem mem_gammaSet_iff {Str : Stretch k c} {s : S} :
    s ∈ gammaSet Str ↔ ∃ x, Str.p ≤ x ∧ x < Str.p + Str.ell ∧ c x = s := by
  simp only [gammaSet, Finset.mem_image, Finset.mem_Ico]
  constructor
  · rintro ⟨x, ⟨h1, h2⟩, h3⟩; exact ⟨x, h1, h2, h3⟩
  · rintro ⟨x, h1, h2, h3⟩; exact ⟨x, ⟨h1, h2⟩, h3⟩

/-- `γ` is a **simple** cycle: it carries `ℓ` distinct states (Step 1 of Lemma 5.3,
`lem:gamma`). -/
theorem gammaSet_card {Str : Stretch k c}
    (hdist : ∀ a b, Str.p ≤ a → a < b → b < Str.p + Str.ell → c a ≠ c b) :
    (gammaSet Str).card = Str.ell := by
  rw [gammaSet, Finset.card_image_of_injOn, Nat.card_Ico]
  · omega
  · intro a ha b hb hab
    simp only [Finset.coe_Ico, Set.mem_Ico] at ha hb
    rcases Nat.lt_trichotomy a b with h | h | h
    · exact absurd hab (hdist a b ha.1 h hb.2)
    · exact h
    · exact absurd hab.symm (hdist b a hb.1 h ha.2)

/-- The states of `γ` are cluster states: by the maximality of the stretch (Step 1 of
Lemma 5.3, `lem:gamma`) all their visits are times of `S`, hence run times. -/
theorem gammaSet_subset_cluster {Str : Stretch k c}
    (hmax : ∀ u, u ≤ 3 * k + 7 → (∃ x, Str.p ≤ x ∧ x < Str.p + Str.ell ∧ c x = c u) →
      Str.p ≤ u ∧ u ≤ Str.q) :
    gammaSet Str ⊆ cluster k c := by
  intro s hs
  obtain ⟨x, hx1, hx2, hx3⟩ := mem_gammaSet_iff.1 hs
  have hp := Str.hp
  have hq := Str.hq
  have hlenS := Str.hlen
  have hell := Str.hell
  have htt := Str.htt
  have hmul : Str.ell ≤ Str.tt * Str.ell := Nat.le_mul_of_pos_left _ htt
  have hst : s ∈ states k c := by
    rw [← hx3]
    exact mem_states (k := k) (c := c) (t := x) (by simp only [times, Finset.mem_range]; omega)
  refine Finset.mem_filter.2 ⟨hst, ?_⟩
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro u hu
  simp only [nvis, Finset.mem_filter, nonRunTimes, Finset.mem_sdiff, times, Finset.mem_range,
    runTimes, Finset.mem_Icc] at hu
  obtain ⟨⟨hun, hurun⟩, hcu⟩ := hu
  have := hmax u (by omega) ⟨x, hx1, hx2, by rw [hx3, hcu]⟩
  exact hurun ⟨by omega, by omega⟩

/-- Every visit of a cluster state off `γ` is a run time outside the stretch
(Step 2 of Lemma 5.3, `lem:gamma`). -/
theorem offCycle_visit {Str : Stretch k c} {s : S} (hs : s ∈ offCycle Str) {u : ℕ}
    (hun : u ≤ 3 * k + 7) (hcu : c u = s) :
    (k ≤ u ∧ u ≤ 2 * k + 5) ∧ (u < Str.p ∨ Str.q < u) := by
  simp only [offCycle, Finset.mem_filter] at hs
  have hrun := cluster_all_visits hs.1 hun hcu
  refine ⟨(mem_rvis.1 hrun).1, ?_⟩
  by_contra hcon
  push_neg at hcon
  obtain ⟨x, hx1, hx2, hx3⟩ := stretch_state Str (u := u) (by omega) (by omega)
  exact hs.2 x (Finset.mem_Ico.2 ⟨hx1, hx2⟩) (by rw [hx3, hcu])

/-- The states of `γ` and the cluster states off `γ` are disjoint (Step 4 of Lemma 5.3,
`lem:gamma`). -/
theorem gamma_offCycle_disjoint {Str : Stretch k c} :
    Disjoint (gammaSet Str) (offCycle Str) := by
  refine Finset.disjoint_left.2 ?_
  intro s hs hs'
  obtain ⟨x, hx1, hx2, hx3⟩ := mem_gammaSet_iff.1 hs
  simp only [offCycle, Finset.mem_filter] at hs'
  exact hs'.2 x (Finset.mem_Ico.2 ⟨hx1, hx2⟩) hx3

/-- `𝒜 = γ ⊔ (𝒜 ∖ γ)`: the cluster is the disjoint union of the states of `γ` and the
cluster states off `γ` (Step 4 of Lemma 5.3, `lem:gamma`). -/
theorem cluster_eq_gamma_union {Str : Stretch k c}
    (hmax : ∀ u, u ≤ 3 * k + 7 → (∃ x, Str.p ≤ x ∧ x < Str.p + Str.ell ∧ c x = c u) →
      Str.p ≤ u ∧ u ≤ Str.q) :
    cluster k c = gammaSet Str ∪ offCycle Str := by
  ext s
  constructor
  · intro hs
    by_cases hg : ∃ x, Str.p ≤ x ∧ x < Str.p + Str.ell ∧ c x = s
    · exact Finset.mem_union_left _ (mem_gammaSet_iff.2 hg)
    · push_neg at hg
      refine Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hs, ?_⟩)
      intro x hx
      rw [Finset.mem_Ico] at hx
      exact hg x hx.1 hx.2
  · intro hs
    rcases Finset.mem_union.1 hs with h | h
    · exact gammaSet_subset_cluster hmax h
    · exact (Finset.mem_filter.1 h).1

/-- `|𝒜| = ℓ + x₁` (Step 4 of Lemma 5.3, `lem:gamma`). -/
theorem cluster_card_eq {Str : Stretch k c}
    (hmax : ∀ u, u ≤ 3 * k + 7 → (∃ x, Str.p ≤ x ∧ x < Str.p + Str.ell ∧ c x = c u) →
      Str.p ≤ u ∧ u ≤ Str.q)
    (hdist : ∀ a b, Str.p ≤ a → a < b → b < Str.p + Str.ell → c a ≠ c b) :
    (cluster k c).card = Str.ell + offCycleCard Str := by
  rw [cluster_eq_gamma_union hmax, Finset.card_union_of_disjoint gamma_offCycle_disjoint,
    gammaSet_card hdist]
  rfl

/-- `|𝒜| ≥ ℓ + x₁`: the cluster contains the `ℓ` states of `γ` and the `x₁` states off
`γ` (Step 4 of Lemma 5.3, `lem:gamma`). -/
theorem ell_add_offCycleCard_le {Str : Stretch k c}
    (hmax : ∀ u, u ≤ 3 * k + 7 → (∃ x, Str.p ≤ x ∧ x < Str.p + Str.ell ∧ c x = c u) →
      Str.p ≤ u ∧ u ≤ Str.q)
    (hdist : ∀ a b, Str.p ≤ a → a < b → b < Str.p + Str.ell → c a ≠ c b) :
    Str.ell + offCycleCard Str ≤ (cluster k c).card :=
  le_of_eq (cluster_card_eq hmax hdist).symm

/-- **Step 2 of Lemma 5.3 (`lem:gamma`), "no second cycle"**, in the form of a statement
about loops.  A closed walk `W[v, v+L]` lying on one side of the stretch, each of whose
states is visited at a second run time, is impossible.  The proof is the primitivity
argument of the source: if the `L` states of the loop are distinct then they are `L`
distinct cluster states off `γ`, so `L ≤ |𝒜| - ℓ ≤ 3 ≤ t` and the loop surgery applies;
otherwise the loop contains a strictly shorter one, and one concludes by induction. -/
theorem no_side_loop (hk : 18 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (hcard : (walkStates (3 * k + 7) c).card ≤ k + 5) (Str : Stretch k c)
    (htt3 : 3 ≤ Str.tt)
    (hmax : ∀ u, u ≤ 3 * k + 7 → (∃ x, Str.p ≤ x ∧ x < Str.p + Str.ell ∧ c x = c u) →
      Str.p ≤ u ∧ u ≤ Str.q)
    (hdist : ∀ a b, Str.p ≤ a → a < b → b < Str.p + Str.ell → c a ≠ c b) :
    ∀ L : ℕ, ∀ v : ℕ, k ≤ v → v + L ≤ 2 * k + 5 → 1 ≤ L → c v = c (v + L) →
      (v + L < Str.p ∨ Str.q < v) →
      (∀ i, i < L → ∃ u, k ≤ u ∧ u ≤ 2 * k + 5 ∧ u ≠ v + i ∧ c u = c (v + i)) → False := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro v hv hvL hL heq hside hsecond
    by_cases hinj : ∀ a b, v ≤ a → a < b → b < v + L → c a ≠ c b
    · -- the loop is simple: its `L` states are distinct cluster states off `γ`
      have hmemoff : ∀ x, v ≤ x → x < v + L → c x ∈ offCycle Str := by
        intro x hx1 hx2
        obtain ⟨u, hu1, hu2, hu3, hu4⟩ := hsecond (x - v) (by omega)
        rw [show v + (x - v) = x by omega] at hu3 hu4
        have hxr : x ∈ rvis k c (c x) := mem_rvis.2 ⟨⟨by omega, by omega⟩, rfl⟩
        have hur : u ∈ rvis k c (c x) := mem_rvis.2 ⟨⟨hu1, hu2⟩, hu4⟩
        have hrv2 : 2 ≤ (rvis k c (c x)).card := by
          have : ({x, u} : Finset ℕ) ⊆ rvis k c (c x) := by
            intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl
            exacts [hxr, hur]
          have hc := Finset.card_le_card this
          rwa [Finset.card_pair (by omega)] at hc
        have hnv : (nvis k c (c x)).card = 0 := by
          by_contra hcon
          have := nvis_rvis_le (by omega : 3 ≤ k) huaw (c x) (by omega)
          omega
        have hst : c x ∈ states k c :=
          mem_states (k := k) (c := c) (t := x) (by simp only [times, Finset.mem_range]; omega)
        refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hst, hnv⟩, ?_⟩
        intro y hy hcy
        rw [Finset.mem_Ico] at hy
        have := hmax x (by omega) ⟨y, hy.1, hy.2, hcy⟩
        omega
      have hcardA : ((Finset.Ico v (v + L)).image c).card = L := by
        rw [Finset.card_image_of_injOn, Nat.card_Ico]
        · omega
        · intro a ha b hb hab
          simp only [Finset.coe_Ico, Set.mem_Ico] at ha hb
          rcases Nat.lt_trichotomy a b with h | h | h
          · exact absurd hab (hinj a b ha.1 h hb.2)
          · exact h
          · exact absurd hab.symm (hinj b a hb.1 h ha.2)
      have hsubA : (Finset.Ico v (v + L)).image c ⊆ offCycle Str := by
        intro s hs
        simp only [Finset.mem_image, Finset.mem_Ico] at hs
        obtain ⟨x, ⟨h1, h2⟩, h3⟩ := hs
        rw [← h3]
        exact hmemoff x h1 h2
      have hLoff : L ≤ offCycleCard Str := by
        have := Finset.card_le_card hsubA
        rw [hcardA] at this
        exact this
      have hbud := ell_add_offCycleCard_le (Str := Str) hmax hdist
      have hcl := cluster_card_le (by omega : 3 ≤ k) huaw hcard
      have hell := Str.hell
      have hLtt : L ≤ Str.tt := by
        simp only [offCycleCard] at hLoff hbud
        omega
      rcases hside with hs | hs
      · exact loop_left_false (by omega) huaw Str hmax hL (by omega) heq (Or.inl hLtt)
      · exact loop_right_false (by omega) huaw Str hmax hL hs (by omega) heq (Or.inl hLtt)
    · -- the loop repeats a state: recurse on the shorter loop
      push_neg at hinj
      obtain ⟨a, b, ha, hab, hb, hcab⟩ := hinj
      refine ih (b - a) (by omega) a (by omega) (by omega) (by omega)
        (by rw [show a + (b - a) = b by omega]; exact hcab) (by omega) ?_
      intro i hi
      obtain ⟨u, hu1, hu2, hu3, hu4⟩ := hsecond (a + i - v) (by omega)
      rw [show v + (a + i - v) = a + i by omega] at hu3 hu4
      exact ⟨u, hu1, hu2, hu3, hu4⟩

/-- **Step 2 of Lemma 5.3 (`lem:gamma`)**: a cluster state off `γ` is visited at most
twice.  A third visit would produce a second cycle `γ'`, i.e. a loop on one side of the
stretch all of whose states are visited twice, which `no_side_loop` excludes. -/
theorem offCycle_rvis_le_two (hk : 18 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (hcard : (walkStates (3 * k + 7) c).card ≤ k + 5) (Str : Stretch k c)
    (htt3 : 3 ≤ Str.tt)
    (hmax : ∀ u, u ≤ 3 * k + 7 → (∃ x, Str.p ≤ x ∧ x < Str.p + Str.ell ∧ c x = c u) →
      Str.p ≤ u ∧ u ≤ Str.q)
    (hdist : ∀ a b, Str.p ≤ a → a < b → b < Str.p + Str.ell → c a ≠ c b)
    {z : S} (hz : z ∈ offCycle Str) : (rvis k c z).card ≤ 2 := by
  by_contra hcon
  have h3 : 3 ≤ (rvis k c z).card := by omega
  have hzc : z ∈ cluster k c := (Finset.mem_filter.1 hz).1
  obtain ⟨e, t₁, tr, he1, ht₁, htr, hspan, hper, hct₁⟩ :=
    cluster_cycle (by omega : 3 ≤ k) huaw hzc h3
  have h2e : t₁ + 2 * e ≤ tr := by
    have : (2 : ℕ) * e ≤ ((rvis k c z).card - 1) * e := Nat.mul_le_mul_right e (by omega)
    omega
  -- the times `t₁`, `t₁+e` and `t₁+2e` are visits of `z`, hence outside the stretch
  have hvisit : ∀ j, j ≤ 2 → c (t₁ + j * e) = z := by
    intro j hj
    have := period_iter hper j t₁ le_rfl (by
      have : j * e ≤ 2 * e := Nat.mul_le_mul_right e hj
      omega)
    rw [← this, hct₁]
  have hout : ∀ j, j ≤ 2 → (t₁ + j * e < Str.p ∨ Str.q < t₁ + j * e) := by
    intro j hj
    have hjb : j * e ≤ 2 * e := Nat.mul_le_mul_right e hj
    exact (offCycle_visit hz (u := t₁ + j * e) (by omega) (hvisit j hj)).2
  have h0 := hout 0 (by omega)
  have h1 := hout 1 (by omega)
  have h2 := hout 2 (by omega)
  simp only [Nat.zero_mul, Nat.add_zero, Nat.one_mul] at h0 h1
  rw [show 2 * e = e + e by ring] at h2
  -- pick a period of the second cycle avoiding the stretch
  rcases h1 with hcase | hcase
  · refine no_side_loop hk huaw hcard Str htt3 hmax hdist e t₁ ht₁ (by omega) he1 ?_
      (Or.inl hcase) ?_
    · exact hper t₁ le_rfl (by omega)
    · intro i hi
      refine ⟨t₁ + e + i, by omega, by omega, by omega, ?_⟩
      have := hper (t₁ + i) (by omega) (by omega)
      rw [show t₁ + i + e = t₁ + e + i by ring] at this
      exact this.symm
  · refine no_side_loop hk huaw hcard Str htt3 hmax hdist e (t₁ + e) (by omega) (by omega)
      he1 ?_ (Or.inr hcase) ?_
    · exact hper (t₁ + e) (by omega) (by omega)
    · intro i hi
      refine ⟨t₁ + i, by omega, by omega, by omega, ?_⟩
      have := hper (t₁ + i) (by omega) (by omega)
      rw [show t₁ + i + e = t₁ + e + i by ring] at this
      exact this

/-!
### Step 4 of Lemma 5.3 (`lem:gamma`): the bookkeeping identities `eq:dzero`
-/

/-- The run visits of the states of `γ` are exactly the times of the stretch, so their
number is `q - p + 1` (Step 4 of Lemma 5.3, `lem:gamma`). -/
theorem gamma_sum_rvis {Str : Stretch k c}
    (hmax : ∀ u, u ≤ 3 * k + 7 → (∃ x, Str.p ≤ x ∧ x < Str.p + Str.ell ∧ c x = c u) →
      Str.p ≤ u ∧ u ≤ Str.q) :
    ∑ s ∈ gammaSet Str, (rvis k c s).card = Str.q + 1 - Str.p := by
  have hp := Str.hp
  have hq := Str.hq
  have hlen := Str.hlen
  have hkey : ∀ s ∈ gammaSet Str,
      (Finset.Icc Str.p Str.q).filter (fun t => c t = s) = rvis k c s := by
    intro s hs
    obtain ⟨x, hx1, hx2, hx3⟩ := mem_gammaSet_iff.1 hs
    ext t
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact mem_rvis.2 ⟨⟨by omega, by omega⟩, h3⟩
    · intro ht
      obtain ⟨⟨h1, h2⟩, h3⟩ := mem_rvis.1 ht
      exact ⟨hmax t (by omega) ⟨x, hx1, hx2, by rw [hx3, h3]⟩, h3⟩
  have hfib := Finset.card_eq_sum_card_fiberwise (f := c) (s := Finset.Icc Str.p Str.q)
    (t := gammaSet Str) (fun t ht => by
      simp only [Finset.coe_Icc, Set.mem_Icc] at ht
      exact mem_gammaSet_iff.2 (stretch_state Str ht.1 ht.2))
  rw [Nat.card_Icc] at hfib
  rw [Finset.sum_congr rfl (fun s hs => congrArg Finset.card (hkey s hs).symm), ← hfib]

/-- Every cluster state off `γ` has at least one run visit. -/
theorem offCycle_rvis_pos {Str : Stretch k c} {z : S} (hz : z ∈ offCycle Str) :
    1 ≤ (rvis k c z).card := by
  have hzc : z ∈ cluster k c := (Finset.mem_filter.1 hz).1
  have hst : z ∈ states k c := (Finset.mem_filter.1 hzc).1
  simp only [states, walkStates, Finset.mem_image, Finset.mem_range] at hst
  obtain ⟨t, ht, hct⟩ := hst
  exact Finset.card_pos.2 ⟨t, cluster_all_visits hzc (by omega) hct⟩

/-- **Step 4 of Lemma 5.3 (`lem:gamma`)**, before Step 5: `d₀ = (x₁ + x_e) + b₁ + r_off`,
where `x₁ + x_e` is written here as the total number of run visits of the cluster states
off `γ`.  The proof combines the count `eq:vA` of the visits to cluster states with the
fact that the visits of the states of `γ` are exactly the `q-p+1` times of the stretch. -/
theorem d0_eq_sum_rvis (hk : 3 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    {Str : Stretch k c}
    (hmax : ∀ u, u ≤ 3 * k + 7 → (∃ x, Str.p ≤ x ∧ x < Str.p + Str.ell ∧ c x = c u) →
      Str.p ≤ u ∧ u ≤ Str.q) :
    Str.d0 = (∑ s ∈ offCycle Str, (rvis k c s).card) + bridgeCount k c + Str.roff := by
  have hsplit : clusterVisits k c
      = (∑ s ∈ gammaSet Str, (rvis k c s).card)
        + ∑ s ∈ offCycle Str, (rvis k c s).card := by
    rw [clusterVisits, cluster_eq_gamma_union hmax, Finset.sum_union gamma_offCycle_disjoint]
  have h1 := gamma_sum_rvis (Str := Str) hmax
  have h2 := count_run hk huaw
  have h3 := Str.d0_add
  have hlen := Str.hlen
  have hp := Str.hp
  have hq := Str.hq
  omega

/-- **Step 4 of Lemma 5.3 (`lem:gamma`)**: `d₀ + ℓ ≤ 7`.  Each of the `x₁` cluster states
off `γ` is visited at most twice (Step 2), so `d₀ ≤ 2x₁ + b₁ + r_off`, and the budget
`eq:budget` together with `|𝒜| = ℓ + x₁` gives `2x₁ + b₁ ≤ 8 - 2ℓ`. -/
theorem d0_add_ell_le (hk : 18 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (hcard : (walkStates (3 * k + 7) c).card ≤ k + 5) (Str : Stretch k c)
    (htt3 : 3 ≤ Str.tt) (hroff : Str.roff < Str.ell)
    (hmax : ∀ u, u ≤ 3 * k + 7 → (∃ x, Str.p ≤ x ∧ x < Str.p + Str.ell ∧ c x = c u) →
      Str.p ≤ u ∧ u ≤ Str.q)
    (hdist : ∀ a b, Str.p ≤ a → a < b → b < Str.p + Str.ell → c a ≠ c b) :
    Str.d0 + Str.ell ≤ 7 := by
  have hle : ∑ s ∈ offCycle Str, (rvis k c s).card ≤ (offCycle Str).card * 2 := by
    have := Finset.sum_le_card_nsmul (offCycle Str) (fun s => (rvis k c s).card) 2
      (fun s hs => offCycle_rvis_le_two hk huaw hcard Str htt3 hmax hdist hs)
    simpa [Nat.smul_one_eq_cast] using this
  have hid := d0_eq_sum_rvis (by omega : 3 ≤ k) huaw (Str := Str) hmax
  have hbud := budget (by omega : 3 ≤ k) huaw hcard
  have hcl := cluster_card_eq (Str := Str) hmax hdist
  simp only [offCycleCard] at hcl
  omega

omit [DecidableEq S] in
/-- `d₀ ≤ t`: the numerical consequence of `d₀ + ℓ ≤ 7` and `d₀ + tℓ = k+5` for `k ≥ 18`
(Step 5 of Lemma 5.3, `lem:gamma`). -/
theorem d0_le_tt (hk : 18 ≤ k) (Str : Stretch k c) (hell4 : Str.ell ≤ 4)
    (h7 : Str.d0 + Str.ell ≤ 7) : Str.d0 ≤ Str.tt := by
  have hadd := Str.d0_add
  have hell := Str.hell
  have hcases : Str.ell = 1 ∨ Str.ell = 2 ∨ Str.ell = 3 ∨ Str.ell = 4 := by omega
  rcases hcases with h | h | h | h <;> rw [h] at hadd h7 <;> omega

/-- **Step 5 of Lemma 5.3 (`lem:gamma`), `x_e = 0`**: every cluster state off `γ` is
visited exactly once.  A second visit would give a closed `b`-labelled walk `κ` on one
side of the stretch, or a shortcut across the stretch, and the corresponding loop surgery
(`loop_left_false`, `loop_right_false`, `loop_span_false`) produces a second accepting
path. -/
theorem offCycle_rvis_eq_one (hk : 18 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (hcard : (walkStates (3 * k + 7) c).card ≤ k + 5) (Str : Stretch k c)
    (hell4 : Str.ell ≤ 4) (htt3 : 3 ≤ Str.tt) (hroff : Str.roff < Str.ell)
    (hmax : ∀ u, u ≤ 3 * k + 7 → (∃ x, Str.p ≤ x ∧ x < Str.p + Str.ell ∧ c x = c u) →
      Str.p ≤ u ∧ u ≤ Str.q)
    (hdist : ∀ a b, Str.p ≤ a → a < b → b < Str.p + Str.ell → c a ≠ c b)
    {z : S} (hz : z ∈ offCycle Str) : (rvis k c z).card = 1 := by
  have h2 := offCycle_rvis_le_two hk huaw hcard Str htt3 hmax hdist hz
  have h1 := offCycle_rvis_pos hz
  have hdtt : Str.d0 ≤ Str.tt :=
    d0_le_tt hk Str hell4 (d0_add_ell_le hk huaw hcard Str htt3 hroff hmax hdist)
  have hp := Str.hp
  have hq := Str.hq
  have hlen := Str.hlen
  have hell := Str.hell
  have htt := Str.htt
  have hmul : Str.ell ≤ Str.tt * Str.ell := Nat.le_mul_of_pos_left _ htt
  have hd0 : Str.d0 = (Str.p - k) + Str.roff + (2 * k + 5 - Str.q) := rfl
  -- the key case: two visits `v₁ < v₂`
  have key : ∀ v₁ v₂ : ℕ, v₁ < v₂ → rvis k c z = {v₁, v₂} → False := by
    intro v₁ v₂ hlt hset
    have hm₁ : v₁ ∈ rvis k c z := by rw [hset]; simp
    have hm₂ : v₂ ∈ rvis k c z := by rw [hset]; simp
    obtain ⟨⟨hk₁, hu₁⟩, hc₁⟩ := mem_rvis.1 hm₁
    obtain ⟨⟨hk₂, hu₂⟩, hc₂⟩ := mem_rvis.1 hm₂
    have hs₁ := (offCycle_visit hz (u := v₁) (by omega) hc₁).2
    have hs₂ := (offCycle_visit hz (u := v₂) (by omega) hc₂).2
    have heq : c v₁ = c (v₁ + (v₂ - v₁)) := by
      rw [show v₁ + (v₂ - v₁) = v₂ by omega, hc₁, hc₂]
    rcases hs₁ with hl₁ | hr₁
    · rcases hs₂ with hl₂ | hr₂
      · -- both visits are before the stretch
        exact loop_left_false (by omega) huaw Str hmax (by omega) (by omega) heq
          (Or.inl (by omega))
      · -- the two visits are on opposite sides of the stretch
        refine loop_span_false (by omega) huaw Str hl₁ hr₂ (by omega)
          (hc₁.trans hc₂.symm) (by simp only [Stretch.slen]; omega) ?_
        have hpos : v₁ + Str.slen v₁ v₂ 0 = Str.p + Str.roff + (v₂ - Str.q) := by
          simp only [Stretch.slen]; omega
        intro hcon
        rw [hc₁] at hcon
        have hmw : v₁ + Str.slen v₁ v₂ 0 ∈ rvis k c z :=
          mem_rvis.2 ⟨⟨by omega, by omega⟩, hcon⟩
        rw [hset] at hmw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmw
        omega
    · -- both visits are after the stretch
      rcases hs₂ with hl₂ | hr₂
      · omega
      · exact loop_right_false (by omega) huaw Str hmax (by omega) hr₁ (by omega) heq
          (Or.inl (by omega))
  rcases (by omega : (rvis k c z).card = 1 ∨ (rvis k c z).card = 2) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab, hset⟩ := Finset.card_eq_two.1 h
    rcases Nat.lt_or_ge a b with hlt | hge
    · exact key a b hlt hset
    · exact key b a (by omega) (by rw [hset, Finset.pair_comm])

/-- **Steps 2, 4 and 5 of Lemma 5.3 (`lem:gamma`)**, in the bookkeeping form `eq:dzero`:
`d₀ = x₁ + b₁ + r_off` and `2(ℓ + x₁) + b₁ + s₀ ≤ 8`. -/
theorem gamma_count (hk : 18 ≤ k) (huaw : IsUAWalk (zw k) (3 * k + 7) c)
    (hcard : (walkStates (3 * k + 7) c).card ≤ k + 5) (Str : Stretch k c)
    (hell4 : Str.ell ≤ 4) (htt3 : 3 ≤ Str.tt) (hroff : Str.roff < Str.ell)
    (hmax : ∀ u, u ≤ 3 * k + 7 → (∃ x, Str.p ≤ x ∧ x < Str.p + Str.ell ∧ c x = c u) →
      Str.p ≤ u ∧ u ≤ Str.q)
    (hdist : ∀ a b, Str.p ≤ a → a < b → b < Str.p + Str.ell → c a ≠ c b) :
    Str.d0 = offCycleCard Str + bridgeCount k c + Str.roff ∧
      2 * (Str.ell + offCycleCard Str) + bridgeCount k c + singleCount k c ≤ 8 := by
  have hsum : ∑ s ∈ offCycle Str, (rvis k c s).card = offCycleCard Str := by
    rw [Finset.sum_congr rfl
      (fun s hs => offCycle_rvis_eq_one hk huaw hcard Str hell4 htt3 hroff hmax hdist hs)]
    simp [offCycleCard]
  refine ⟨?_, ?_⟩
  · rw [← hsum]
    exact d0_eq_sum_rvis (by omega) huaw hmax
  · have hbud := budget (by omega : 3 ≤ k) huaw hcard
    rwa [cluster_card_eq hmax hdist] at hbud

end

end AneVsAn
