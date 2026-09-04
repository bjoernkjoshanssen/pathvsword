# Verification code for "Exact beats unique infinitely often"

Word family: z_k = a_1...a_k b^(k+5) c a_1...a_{k-1} d e,  k ≡ 0 (mod 3).
(z_3 = 0123333333340156 under renaming.)

## Files

- `an_tools.py` — path counting, exact-acceptance checking (subset word
  count), accepting-path counting; plus a small reference implementation
  of A_N via walk enumeration for short words.
- `an_search.c` — exhaustive branch-and-bound over uniquely-accepting
  walks (restricted-growth colorings, sound path-count pruning).
  Usage: ./an_search <word (base-36 digits)> <max states>
  Establishes: no (k+5)-state uniquely accepting walk for z_k,
  k = 3,6,9,12,15 (words as printed by family.py).
- `brute_an.c` — brute force over ALL small NFAs (validation of
  an_search on short binary words).
- `ane_sat.py` — SAT encoding of exact acceptance (needs python-sat);
  rediscovers the 8-state exact NFA for z_3 ab initio.
- `family.py` — builds z_k and the (k+5)-state exact acceptor M_k;
  verifies exactness and counts accepting paths (3 for every k).
- `boundary_scan.py` — enumerates the endgame boundary schemas
  (S0/S1a/S1b/S2a/S2b) for cluster shapes l = 1,2,4 at
  k = 12,...,30 and verifies every instance has >= 2 accepting paths.

## Key results reproduced

    python3 family.py                # M_k exact, 3 paths, k = 4..11 (C=k+1)
    gcc -O2 -o an_search an_search.c
    ./an_search 0123333333340156 8   # UNSAT -> A_N(z_3) >= 9
    ./an_search 0123333333340156 9   # witness -> A_N(z_3) = 9
    python3 boundary_scan.py         # all boundary schemas die
