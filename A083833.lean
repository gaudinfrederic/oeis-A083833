import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# OEIS A083833 - Branicky's conjectures on palindromes `p` with `5p+1` palindrome

Statement (OEIS): palindromes `p` such that `5p+1` is also a palindrome.
Branicky (Jun 2021), tagged "(Conjectures)":
  (C1) all terms use only digits `{0,1,2,3}`.
  (C2) for `d` even, the only `d`-digit term is `22...2` (i.e. every term
       starting with `1` has odd length).

Mechanism (carry chain). `a j = (p / 10^j) % 10` little-endian digits,
`m` the digit length. Closed-form carry `c j = (5 * (p % 10^j) + 1) / 10^j`
(`c 0 = 1` folds the `+1`, `c j ≤ 4`). Then
`q j = ((5p+1) / 10^j) % 10 = (5 a j + c j) % 10` and
`c (j+1) = (5 a j + c j) / 10`. With `q = 5p+1` palindromic of length
`m' ∈ {m, m+1}`:

* `m' = m`  ⟹ carry chain symmetric `c j = c (m-1-j)`, hence 2-periodic
  (`c (j+1) = c (j-1)`), forcing `m` odd, `a 0 = 1`, and
  `a j ∈ {0,1}` (`j` even) / `a j ∈ {2,3}` (`j` odd).
* `m' = m+1` ⟹ `c (m-j) = c j`, all digits same parity, and the swap
  `g(u,a)=w ∧ g(w,a)=u` has no solution for `u≠w` (`11|u-w| ≤ 9`), so
  the chain is constant `c j = v`; boundary forces `v = 1`, `a_0 = 2`,
  hence `p = 22...2`.
-/

namespace A083833

/-- The `j`-th decimal digit of `n` (units = `j = 0`). -/
def dgt (n j : ℕ) : ℕ := n / 10 ^ j % 10

/-- `p` has `m`-digit palindromic decimal expansion: symmetric digits,
`10^(m-1) ≤ p < 10^m`. -/
structure IsPal (p m : ℕ) : Prop where
  sym : ∀ j < m, dgt p j = dgt p (m - 1 - j)
  lo : 10 ^ (m - 1) ≤ p
  hi : p < 10 ^ m

/-- Closed-form carry into position `j` when computing `5p+1`. -/
def crry (p j : ℕ) : ℕ := (5 * (p % 10 ^ j) + 1) / 10 ^ j

theorem crry_zero (p : ℕ) : crry p 0 = 1 := by
  unfold crry
  rw [pow_zero, Nat.mod_one]
  norm_num

theorem crry_le (p j : ℕ) : crry p j ≤ 4 := by
  have h : p % 10 ^ j < 10 ^ j := Nat.mod_lt _ (by positivity)
  have h10 : 0 < 10 ^ j := by positivity
  unfold crry
  have := (Nat.div_lt_iff_lt_mul h10).mpr (show 5 * (p % 10 ^ j) + 1 < 5 * 10 ^ j by omega)
  omega

/-- Core identity: `5p+1 = 10^j * (5 Q + c_j) + r` with `r < 10^j`. -/
theorem decomp (p j : ℕ) :
    5 * p + 1 = 10 ^ j * (5 * (p / 10 ^ j) + crry p j) +
      (5 * (p % 10 ^ j) + 1) % 10 ^ j := by
  have h1 : p = 10 ^ j * (p / 10 ^ j) + p % 10 ^ j := (Nat.div_add_mod p _).symm
  have h2 : 5 * (p % 10 ^ j) + 1 =
      10 ^ j * ((5 * (p % 10 ^ j) + 1) / 10 ^ j) + (5 * (p % 10 ^ j) + 1) % 10 ^ j :=
    (Nat.div_add_mod _ _).symm
  unfold crry
  have e3 : 10 ^ j * (5 * (p / 10 ^ j) + (5 * (p % 10 ^ j) + 1) / 10 ^ j) =
      5 * (10 ^ j * (p / 10 ^ j)) + 10 ^ j * ((5 * (p % 10 ^ j) + 1) / 10 ^ j) := by
    ring
  rw [e3]
  omega

/-- The quotient of `5p+1` by `10^j`. -/
theorem div_ten_pow (p j : ℕ) :
    (5 * p + 1) / 10 ^ j = 5 * (p / 10 ^ j) + crry p j := by
  have h := decomp p j
  have hr : (5 * (p % 10 ^ j) + 1) % 10 ^ j < 10 ^ j :=
    Nat.mod_lt _ (by positivity)
  rw [h]
  refine Nat.div_eq_of_lt_le ?_ ?_
  · have mc : (5 * (p / 10 ^ j) + crry p j) * 10 ^ j =
        10 ^ j * (5 * (p / 10 ^ j) + crry p j) := mul_comm _ _
    omega
  · have e : (5 * (p / 10 ^ j) + crry p j + 1) * 10 ^ j =
        10 ^ j * (5 * (p / 10 ^ j) + crry p j) + 10 ^ j := by ring
    rw [e]; omega

/-- Digits of `5p+1` in terms of digits of `p` and carries. -/
theorem qdgt (p j : ℕ) :
    dgt (5 * p + 1) j = (5 * dgt p j + crry p j) % 10 := by
  unfold dgt
  rw [div_ten_pow]
  have : p / 10 ^ j = 10 * (p / 10 ^ j / 10) + p / 10 ^ j % 10 :=
    (Nat.div_add_mod _ _).symm
  omega

/-- Carry recurrence. -/
theorem crry_succ (p j : ℕ) :
    crry p (j + 1) = (5 * dgt p j + crry p j) / 10 := by
  have hmod : p % 10 ^ (j + 1) = p % 10 ^ j + 10 ^ j * (p / 10 ^ j % 10) := by
    have e1 : p / (10 ^ j * 10) = p / 10 ^ j / 10 := (Nat.div_div_eq_div_mul _ _ _).symm
    have e4 : p = 10 ^ j * 10 * (p / (10 ^ j * 10)) + p % (10 ^ j * 10) :=
      (Nat.div_add_mod p _).symm
    have e3 : p = 10 ^ j * (p / 10 ^ j) + p % 10 ^ j := (Nat.div_add_mod p _).symm
    have e2 : p / 10 ^ j = 10 * (p / (10 ^ j * 10)) + p / 10 ^ j % 10 := by
      rw [e1]; omega
    have e5 : 10 ^ j * (p / 10 ^ j) =
        10 * (10 ^ j * (p / (10 ^ j * 10))) + 10 ^ j * (p / 10 ^ j % 10) := by
      conv_lhs => rw [e2]
      ring
    have e7 : 10 ^ j * 10 * (p / (10 ^ j * 10)) =
        10 * (10 ^ j * (p / (10 ^ j * 10))) := by ring
    have hX : (10 : ℕ) ^ (j + 1) = 10 ^ j * 10 := by rw [pow_succ]
    rw [hX]
    omega
  unfold crry dgt
  rw [hmod]
  have hX : (0 : ℕ) < 10 ^ j := by positivity
  have hr : (5 * (p % 10 ^ j) + 1) % 10 ^ j < 10 ^ j := Nat.mod_lt _ hX
  have hdec : 5 * (p % 10 ^ j) + 1 =
      10 ^ j * ((5 * (p % 10 ^ j) + 1) / 10 ^ j) + (5 * (p % 10 ^ j) + 1) % 10 ^ j :=
    (Nat.div_add_mod _ _).symm
  have e5 : 5 * (p % 10 ^ j + 10 ^ j * (p / 10 ^ j % 10)) + 1 =
      10 ^ j * (5 * (p / 10 ^ j % 10) + (5 * (p % 10 ^ j) + 1) / 10 ^ j) +
      (5 * (p % 10 ^ j) + 1) % 10 ^ j := by
    have e6 : 10 ^ j * (5 * (p / 10 ^ j % 10) + (5 * (p % 10 ^ j) + 1) / 10 ^ j) =
        10 ^ j * (5 * (p / 10 ^ j % 10)) + 10 ^ j * ((5 * (p % 10 ^ j) + 1) / 10 ^ j) := by
      ring
    have e7 : 10 ^ j * (5 * (p / 10 ^ j % 10)) = 5 * (10 ^ j * (p / 10 ^ j % 10)) := by
      ring
    rw [e6]; omega
  rw [e5]
  have hX : (10 : ℕ) ^ (j + 1) = 10 ^ j * 10 := by rw [pow_succ]
  rw [hX]
  -- now: (10^j * Y + r) / (10^j * 10) = Y / 10 where Y = 5a+c, r < 10^j
  refine Nat.div_eq_of_lt_le ?_ ?_
  · -- Y/10 * (10^j*10) ≤ 10^j * Y + r
    have hY : 10 * ((5 * (p / 10 ^ j % 10) + (5 * (p % 10 ^ j) + 1) / 10 ^ j) / 10) ≤
        5 * (p / 10 ^ j % 10) + (5 * (p % 10 ^ j) + 1) / 10 ^ j := by omega
    have e1 : (5 * (p / 10 ^ j % 10) + (5 * (p % 10 ^ j) + 1) / 10 ^ j) / 10 *
        (10 ^ j * 10) = 10 * (10 ^ j *
        ((5 * (p / 10 ^ j % 10) + (5 * (p % 10 ^ j) + 1) / 10 ^ j) / 10)) := by ring
    have e2 : 10 ^ j * (10 * ((5 * (p / 10 ^ j % 10) +
        (5 * (p % 10 ^ j) + 1) / 10 ^ j) / 10)) =
        10 * (10 ^ j * ((5 * (p / 10 ^ j % 10) +
        (5 * (p % 10 ^ j) + 1) / 10 ^ j) / 10)) := by ring
    have e3 : 10 ^ j * (10 * ((5 * (p / 10 ^ j % 10) +
        (5 * (p % 10 ^ j) + 1) / 10 ^ j) / 10)) ≤
        10 ^ j * (5 * (p / 10 ^ j % 10) + (5 * (p % 10 ^ j) + 1) / 10 ^ j) := by
      gcongr
    omega
  · -- 10^j * Y + r < (Y/10 + 1) * (10^j*10)
    have hYd : 5 * (p / 10 ^ j % 10) + (5 * (p % 10 ^ j) + 1) / 10 ^ j =
        10 * ((5 * (p / 10 ^ j % 10) + (5 * (p % 10 ^ j) + 1) / 10 ^ j) / 10) +
        (5 * (p / 10 ^ j % 10) + (5 * (p % 10 ^ j) + 1) / 10 ^ j) % 10 :=
      (Nat.div_add_mod _ _).symm
    have hY : (5 * (p / 10 ^ j % 10) + (5 * (p % 10 ^ j) + 1) / 10 ^ j) % 10 ≤ 9 := by
      omega
    have e1 : ((5 * (p / 10 ^ j % 10) + (5 * (p % 10 ^ j) + 1) / 10 ^ j) / 10 + 1) *
        (10 ^ j * 10) = 10 * (10 ^ j *
        ((5 * (p / 10 ^ j % 10) + (5 * (p % 10 ^ j) + 1) / 10 ^ j) / 10)) + 10 * 10 ^ j := by
      ring
    have e2 : 10 ^ j * (5 * (p / 10 ^ j % 10) + (5 * (p % 10 ^ j) + 1) / 10 ^ j) =
        10 * (10 ^ j * ((5 * (p / 10 ^ j % 10) + (5 * (p % 10 ^ j) + 1) / 10 ^ j) / 10)) +
        10 ^ j * ((5 * (p / 10 ^ j % 10) + (5 * (p % 10 ^ j) + 1) / 10 ^ j) % 10) := by
      conv_lhs => rw [hYd]
      ring
    have e3 : 10 ^ j * ((5 * (p / 10 ^ j % 10) + (5 * (p % 10 ^ j) + 1) / 10 ^ j) % 10) ≤
        9 * 10 ^ j := by
      rw [mul_comm (10 ^ j) ((5 * (p / 10 ^ j % 10) + (5 * (p % 10 ^ j) + 1) / 10 ^ j) % 10)]
      gcongr
    omega

/-- `dgt` vanishes above the length. -/
theorem dgt_eq_zero_of_ge {p m j : ℕ} (h : p < 10 ^ m) (hj : m ≤ j) : dgt p j = 0 := by
  unfold dgt
  have : p < 10 ^ j := lt_of_lt_of_le h (pow_le_pow_right₀ (by norm_num) hj)
  rw [Nat.div_eq_of_lt this, Nat.zero_mod]

/-- Length of `5p+1` is `m` or `m+1`. -/
theorem mp_cases {p m m' : ℕ} (hp : IsPal p m) (hq : IsPal (5 * p + 1) m')
    (hm : 1 ≤ m) : m' = m ∨ m' = m + 1 := by
  have hphi := hp.hi
  have hplo := hp.lo
  have hqhi := hq.hi
  have hqlo := hq.lo
  have hup : 5 * p + 1 < 10 ^ (m + 1) := by
    calc 5 * p + 1 < 5 * 10 ^ m := by omega
      _ < 10 ^ (m + 1) := by rw [pow_succ']; omega
  have hlo : 10 ^ (m - 1) < 5 * p + 1 := by omega
  -- m' ≤ m+1
  have h1 : m' - 1 < m + 1 := by
    by_contra h
    replace h := not_lt.mp h
    have : 10 ^ (m + 1) ≤ 10 ^ (m' - 1) := pow_le_pow_right₀ (by norm_num) h
    omega
  -- m' ≥ m
  have h2 : m ≤ m' := by
    by_contra h
    replace h := not_le.mp h
    have : m' ≤ m - 1 := by omega
    have : 10 ^ m' ≤ 10 ^ (m - 1) := pow_le_pow_right₀ (by norm_num) this
    omega
  omega

/-- `m' = m` iff the top carry vanishes. -/
theorem crry_m_eq_zero_iff {p m : ℕ} (hp : p < 10 ^ m) :
    crry p m = 0 ↔ 5 * p + 1 < 10 ^ m := by
  unfold crry
  rw [Nat.mod_eq_of_lt hp, Nat.div_eq_zero_iff,
      or_iff_right (pow_ne_zero _ (by norm_num) : (10 : ℕ) ^ m ≠ 0)]

/-- Carry symmetry, same-length case: `c_j = c_{m-1-j}`. -/
theorem crry_sym_same {p m : ℕ} (hp : IsPal p m) (hq : IsPal (5 * p + 1) m)
    {j : ℕ} (hj : j < m) : crry p j = crry p (m - 1 - j) := by
  have e := hq.sym j (by omega)
  rw [qdgt, qdgt] at e
  have ha : dgt p (m - 1 - j) = dgt p j := (hp.sym j hj).symm
  rw [ha] at e
  have c1 := crry_le p j
  have c2 := crry_le p (m - 1 - j)
  omega

/-- Carry symmetry, length+1 case: `c_{m-j} = c_j` for `1 ≤ j ≤ m-1`. -/
theorem crry_sym_succ {p m : ℕ} (hp : IsPal p m) (hq : IsPal (5 * p + 1) (m + 1))
    {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ m - 1) : crry p (m - j) = crry p j := by
  have e := hq.sym j (by omega)
  have hm_j : m + 1 - 1 - j = m - j := by omega
  rw [hm_j, qdgt, qdgt] at e
  have ha : dgt p (m - j) = dgt p (j - 1) := by
    have h := hp.sym (j - 1) (by omega)
    rw [show m - 1 - (j - 1) = m - j by omega] at h
    exact h.symm
  rw [ha] at e
  have c1 := crry_le p j
  have c2 := crry_le p (m - j)
  omega

/-- Digit parity, length+1 case: `a_j ≡ a_{j-1} (mod 2)` for `1 ≤ j ≤ m-1`. -/
theorem dgt_parity_succ {p m : ℕ} (hp : IsPal p m) (hq : IsPal (5 * p + 1) (m + 1))
    {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ m - 1) : dgt p j % 2 = dgt p (j - 1) % 2 := by
  have e := hq.sym j (by omega)
  have hm_j : m + 1 - 1 - j = m - j := by omega
  rw [hm_j, qdgt, qdgt] at e
  have ha : dgt p (m - j) = dgt p (j - 1) := by
    have h := hp.sym (j - 1) (by omega)
    rw [show m - 1 - (j - 1) = m - j by omega] at h
    exact h.symm
  rw [ha] at e
  have c1 := crry_le p j
  have c2 := crry_le p (m - j)
  omega

/-- No nontrivial 2-cycle: `g(u,a)=w` and `g(w,a)=u` force `u=w`,
hence `c_{j+1} = c_j` for `1 ≤ j ≤ m-2`. -/
theorem carry_const_succ {p m : ℕ} (hp : IsPal p m) (hq : IsPal (5 * p + 1) (m + 1))
    {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ m - 2) (hm : 2 ≤ m) :
    crry p (j + 1) = crry p j := by
  have e1 := crry_succ p j
  have hs1 := crry_sym_succ hp hq (show 1 ≤ j + 1 by omega) (show j + 1 ≤ m - 1 by omega)
  have hs0 := crry_sym_succ hp hq hj1 (show j ≤ m - 1 by omega)
  have e2 := crry_succ p (m - 1 - j)
  have hidx : m - 1 - j + 1 = m - j := by omega
  rw [hidx] at e2
  have ha : dgt p (m - 1 - j) = dgt p j := (hp.sym j (by omega)).symm
  have hc : crry p (m - 1 - j) = crry p (j + 1) := by
    rw [show m - 1 - j = m - (j + 1) by omega]
    exact hs1
  rw [ha, hc] at e2
  have c1 := crry_le p j
  have c2 := crry_le p (j + 1)
  have c3 := crry_le p (m - j)
  omega

/-- Same-length case: 2-periodicity `c_{j+1} = c_{j-1}` for `1 ≤ j ≤ m-2`. -/
theorem carry_period_same {p m : ℕ} (hp : IsPal p m) (hq : IsPal (5 * p + 1) m)
    {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ m - 2) :
    crry p (j + 1) = crry p (j - 1) := by
  have e1 := crry_succ p j
  have e2 := crry_succ p (m - 1 - j)
  have hidx : m - 1 - j + 1 = m - j := by omega
  rw [hidx] at e2
  have ha : dgt p (m - 1 - j) = dgt p j := (hp.sym j (by omega)).symm
  have hc : crry p (m - 1 - j) = crry p j :=
    (crry_sym_same hp hq (show j < m by omega)).symm
  rw [ha, hc] at e2
  have hsym : crry p (m - j) = crry p (j - 1) := by
    rw [show m - j = m - 1 - (j - 1) by omega]
    exact (crry_sym_same hp hq (j := j - 1) (by omega)).symm
  rw [hsym, ← e1] at e2
  exact e2.symm

/-- Same-length case: even-indexed carries equal `1`. -/
theorem carry_even_same {p m : ℕ} (hp : IsPal p m) (hq : IsPal (5 * p + 1) m) :
    ∀ k, 2 * k ≤ m - 1 → crry p (2 * k) = 1 := by
  intro k
  induction k with
  | zero => intro _; exact crry_zero p
  | succ k ih =>
    intro hk
    have hstep := carry_period_same hp hq (j := 2 * k + 1) (by omega) (by omega)
    have e1 : 2 * k + 1 + 1 = 2 * (k + 1) := by ring
    have e2 : 2 * k + 1 - 1 = 2 * k := by omega
    rw [e1, e2] at hstep
    rw [hstep, ih (by omega)]

/-- Same-length case: odd-indexed carries all equal `c_1`. -/
theorem carry_odd_same {p m : ℕ} (hp : IsPal p m) (hq : IsPal (5 * p + 1) m) :
    ∀ k, 2 * k + 1 ≤ m - 1 → crry p (2 * k + 1) = crry p 1 := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have hstep := carry_period_same hp hq (j := 2 * k + 2) (by omega) (by omega)
    have e1 : 2 * k + 2 + 1 = 2 * (k + 1) + 1 := by ring
    have e2 : 2 * k + 2 - 1 = 2 * k + 1 := by omega
    rw [e1, e2] at hstep
    rw [hstep, ih (by omega)]

/-- Same-length case: `m` must be odd and `a_0 = 1`. -/
theorem same_case_odd_a0 {p m : ℕ} (hp : IsPal p m) (hq : IsPal (5 * p + 1) m)
    (hm : 1 ≤ m) : Odd m ∧ dgt p 0 = 1 := by
  have hcm0 : crry p m = 0 := by
    rw [crry_m_eq_zero_iff hp.hi]; exact hq.hi
  -- top digit nonzero
  have htop : 1 ≤ dgt p (m - 1) := by
    have h1 : 1 ≤ p / 10 ^ (m - 1) := Nat.div_pos hp.lo (by positivity)
    have h2 : p / 10 ^ (m - 1) < 10 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity : (0:ℕ) < 10 ^ (m - 1))]
      have e : (10 : ℕ) ^ m = 10 * 10 ^ (m - 1) := by
        cases m with
        | zero => omega
        | succ k => rw [pow_succ, show k + 1 - 1 = k by omega]; ring
      have hphi := hp.hi
      omega
    unfold dgt
    omega
  have htop0 : dgt p 0 = dgt p (m - 1) := by
    have h := hp.sym 0 (by omega)
    rw [show m - 1 - 0 = m - 1 by omega] at h
    exact h
  by_cases hpar : m % 2 = 0
  · -- m even: derive contradiction
    obtain ⟨k, hk⟩ : ∃ k, m = 2 * k := ⟨m / 2, by omega⟩
    have hk1 : 1 ≤ k := by omega
    have csym := crry_sym_same hp hq (j := 0) (by omega)
    rw [show m - 1 - 0 = m - 1 by omega, crry_zero] at csym
    -- csym : 1 = crry p (m - 1)
    have codd := carry_odd_same hp hq (k - 1) (by omega)
    rw [show 2 * (k - 1) + 1 = m - 1 by omega] at codd
    -- codd : crry p (m - 1) = crry p 1 → c_1 = 1
    have hc1 : crry p 1 = 1 := by rw [← csym] at codd; exact codd.symm
    have e1 : 1 = (5 * dgt p 0 + 1) / 10 := by
      have e := crry_succ p 0
      rw [crry_zero] at e
      have e' : crry p 1 = (5 * dgt p 0 + 1) / 10 := e
      omega
    have em := crry_succ p (m - 1)
    have hsym2 : crry p (m - 1) = 1 := csym.symm
    rw [show m - 1 + 1 = m by omega, ← htop0, hsym2] at em
    -- em : c_m = (5 a_0 + 1)/10 = 1 ≠ 0 = hcm0
    omega
  · -- m odd: a_0 = 1
    refine ⟨Nat.odd_iff.mpr (by omega), ?_⟩
    have hmk : m - 1 = 2 * ((m - 1) / 2) := by omega
    have ceven := carry_even_same hp hq ((m - 1) / 2) (by omega)
    rw [← hmk] at ceven
    have em := crry_succ p (m - 1)
    rw [show m - 1 + 1 = m by omega, ← htop0, ceven, hcm0] at em
    -- em : 0 = (5 a_0 + 1)/10 → a_0 ≤ 1; a_0 ≥ 1 (top)
    have htop' : 1 ≤ dgt p 0 := by rw [htop0]; exact htop
    omega

/-- Same-length case: digit classes. -/
theorem same_case_digits {p m : ℕ} (hp : IsPal p m) (hq : IsPal (5 * p + 1) m)
    (hm : 1 ≤ m) :
    (∀ j, j < m → j % 2 = 0 → dgt p j ≤ 1) ∧
    (∀ j, j < m → j % 2 = 1 → 2 ≤ dgt p j ∧ dgt p j ≤ 3) := by
  obtain ⟨hmo, ha0⟩ := same_case_odd_a0 hp hq hm
  have hcm0 : crry p m = 0 := by
    rw [crry_m_eq_zero_iff hp.hi]; exact hq.hi
  have hc1 : crry p 1 = 0 := by
    have e := crry_succ p 0
    rw [crry_zero, ha0] at e
    have e' : crry p 1 = (5 * 1 + 1) / 10 := e
    omega
  refine ⟨?_, ?_⟩
  · intro j hj hev
    -- c_j = 1 (even index), c_{j+1} = 0
    have cj : crry p j = 1 := by
      obtain ⟨k, hk⟩ : ∃ k, j = 2 * k := ⟨j / 2, by omega⟩
      rw [hk]
      exact carry_even_same hp hq k (by omega)
    have e := crry_succ p j
    rw [cj] at e
    by_cases hjm : j + 1 ≤ m - 1
    · have cj1 : crry p (j + 1) = 0 := by
        have hje : j + 1 = 2 * (j / 2) + 1 := by omega
        rw [hje]
        rw [carry_odd_same hp hq (j / 2) (by omega)]
        exact hc1
      omega
    · have hjm2 : j + 1 = m := by omega
      rw [hjm2, hcm0] at e
      omega
  · intro j hj hod
    have cj : crry p j = 0 := by
      obtain ⟨k, hk⟩ : ∃ k, j = 2 * k + 1 := ⟨(j - 1) / 2, by omega⟩
      rw [hk]
      rw [carry_odd_same hp hq k (by omega)]
      exact hc1
    have e := crry_succ p j
    rw [cj] at e
    -- j odd, m odd → j ≤ m-2 → j+1 ≤ m-1, j+1 even → c_{j+1}=1
    have hjm : j + 1 ≤ m - 1 := by
      obtain ⟨t, ht⟩ := hmo
      omega
    have cj1 : crry p (j + 1) = 1 := by
      have hje : j + 1 = 2 * ((j + 1) / 2) := by omega
      rw [hje]
      exact carry_even_same hp hq ((j + 1) / 2) (by omega)
    rw [cj1] at e
    unfold dgt at e ⊢
    omega

/-- Length+1 case: every digit is `2`. -/
theorem succ_case_all2 {p m : ℕ} (hp : IsPal p m) (hq : IsPal (5 * p + 1) (m + 1))
    (hm : 1 ≤ m) : ∀ j < m, dgt p j = 2 := by
  -- boundary: q_0 = q_m  →  (5 a_0 + 1) % 10 = c_m
  have hb := hq.sym 0 (by omega : 0 < m + 1)
  rw [show m + 1 - 1 - 0 = m by omega, qdgt, qdgt, crry_zero] at hb
  have hdm0 : dgt p m = 0 := dgt_eq_zero_of_ge hp.hi le_rfl
  have hcm9 : crry p m < 10 := lt_of_le_of_lt (crry_le p m) (by norm_num)
  rw [hdm0, show (5 * 0 + crry p m) % 10 = crry p m by omega] at hb
  -- c_1 = v = (5 a_0 + 1)/10
  have e0 : crry p 1 = (5 * dgt p 0 + 1) / 10 := by
    have e := crry_succ p 0
    rw [crry_zero] at e
    exact e
  -- constant chain: c_1 = ... = c_{m-1}
  have hconst : ∀ j, 1 ≤ j → j ≤ m - 1 → crry p j = crry p 1 := by
    intro j hj1
    induction j, hj1 using Nat.le_induction with
    | base => intro _; rfl
    | succ k hk ih =>
      intro hkm
      have hs := carry_const_succ hp hq (j := k) hk (by omega) (by omega)
      rw [hs]
      exact ih (by omega)
  have ham1 : dgt p (m - 1) = dgt p 0 := by
    have h := hp.sym 0 (by omega)
    rw [show m - 1 - 0 = m - 1 by omega] at h
    exact h.symm
  -- boundary equations → a_0 = 2, v = 1
  have hbnd : dgt p 0 = 2 ∧ crry p 1 = 1 := by
    have h91 : dgt p 0 ≤ 9 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
    by_cases hm1 : m = 1
    · subst hm1
      have h2 : dgt p 0 = 2 := by omega
      have hc : crry p 1 = 1 := by
        rw [h2] at e0
        omega
      exact ⟨h2, hc⟩
    · have hcm1 : crry p (m - 1) = crry p 1 := hconst (m - 1) (by omega) (by omega)
      have em := crry_succ p (m - 1)
      rw [show m - 1 + 1 = m by omega, ham1, hcm1] at em
      have hcm4 : crry p m ≤ 4 := crry_le p m
      have hc14 : crry p 1 ≤ 4 := crry_le p 1
      have h2 : dgt p 0 = 2 ∧ crry p 1 = 1 ∧ crry p m = 1 := by
        refine ⟨?_, ?_, ?_⟩ <;> omega
      exact ⟨h2.1, h2.2.1⟩
  obtain ⟨ha0, hv1⟩ := hbnd
  -- parity of all digits = parity of a_0
  have hparall : ∀ j, j ≤ m - 1 → dgt p j % 2 = dgt p 0 % 2 := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      have hs := dgt_parity_succ hp hq (j := j + 1) (by omega) (by omega)
      rw [show j + 1 - 1 = j by omega] at hs
      rw [hs]
      exact ih (by omega)
  intro j hj
  by_cases hj0 : j = 0
  · subst hj0; exact ha0
  · -- j ∈ [1,m-1]: c_j = 1 and c_{j+1} ∈ {1, c_m}
    have hjv : crry p j = 1 := by rw [hconst j (by omega) (by omega), hv1]
    have ej := crry_succ p j
    rw [hjv] at ej
    have hjv1 : crry p (j + 1) = 1 := by
      by_cases hjm : j + 1 ≤ m - 1
      · rw [hconst (j + 1) (by omega) hjm, hv1]
      · have hje : j + 1 = m := by omega
        rw [hje]
        have hcm1 : crry p (m - 1) = 1 := by
          rw [hconst (m - 1) (by omega) (by omega), hv1]
        have em := crry_succ p (m - 1)
        rw [show m - 1 + 1 = m by omega, ham1, ha0, hcm1] at em
        rw [em]
    rw [hjv1] at ej
    -- ej : 1 = (5 a_j + 1)/10 → a_j ∈ {2,3}; parity a_j ≡ a_0 = 2 → a_j = 2
    have hpar := hparall j (by omega)
    rw [ha0] at hpar
    omega

/-- **Conjecture C1**: every digit of `p` is `≤ 3`. -/
theorem A083833_C1 {p m m' : ℕ} (hp : IsPal p m) (hq : IsPal (5 * p + 1) m')
    (hm : 1 ≤ m) : ∀ j < m, dgt p j ≤ 3 := by
  rcases mp_cases hp hq hm with h | h
  · subst h
    have ⟨d1, d2⟩ := same_case_digits hp hq hm
    intro j hj
    by_cases hjev : j % 2 = 0
    · exact le_trans (d1 j hj hjev) (by norm_num)
    · have hod : j % 2 = 1 := by omega
      exact (d2 j hj hod).2
  · subst h
    intro j hj
    have h2 := succ_case_all2 hp hq hm j hj
    omega

/-- **Conjecture C2**: for `m` even, every digit of `p` is `2` (`p = 22...2`). -/
theorem A083833_C2 {p m m' : ℕ} (hp : IsPal p m) (hq : IsPal (5 * p + 1) m')
    (hm : 1 ≤ m) (hme : m % 2 = 0) : ∀ j < m, dgt p j = 2 := by
  rcases mp_cases hp hq hm with h | h
  · subst h
    obtain ⟨hodd, _⟩ := same_case_odd_a0 hp hq hm
    rw [Nat.odd_iff] at hodd
    omega
  · subst h
    exact succ_case_all2 hp hq hm

/-- Same-length case: `c_1 = 0`. -/
theorem same_case_c1 {p m : ℕ} (hp : IsPal p m) (hq : IsPal (5 * p + 1) m)
    (hm : 1 ≤ m) : crry p 1 = 0 := by
  have ha0 := (same_case_odd_a0 hp hq hm).2
  have e := crry_succ p 0
  rw [crry_zero, ha0] at e
  have e' : crry p 1 = (5 * 1 + 1) / 10 := e
  omega

/-- Length+1 case: the whole carry chain equals `1` up to `c_m`. -/
theorem succ_case_carry {p m : ℕ} (hp : IsPal p m) (hq : IsPal (5 * p + 1) (m + 1))
    (hm : 1 ≤ m) : ∀ j ≤ m, crry p j = 1 := by
  have hb := hq.sym 0 (by omega : 0 < m + 1)
  rw [show m + 1 - 1 - 0 = m by omega, qdgt, qdgt, crry_zero] at hb
  have hdm0 : dgt p m = 0 := dgt_eq_zero_of_ge hp.hi le_rfl
  have hcm9 : crry p m < 10 := lt_of_le_of_lt (crry_le p m) (by norm_num)
  rw [hdm0, show (5 * 0 + crry p m) % 10 = crry p m by omega] at hb
  have e0 : crry p 1 = (5 * dgt p 0 + 1) / 10 := by
    have e := crry_succ p 0
    rw [crry_zero] at e
    exact e
  have hconst : ∀ j, 1 ≤ j → j ≤ m - 1 → crry p j = crry p 1 := by
    intro j hj1
    induction j, hj1 using Nat.le_induction with
    | base => intro _; rfl
    | succ k hk ih =>
      intro hkm
      have hs := carry_const_succ hp hq (j := k) hk (by omega) (by omega)
      rw [hs]
      exact ih (by omega)
  have ham1 : dgt p (m - 1) = dgt p 0 := by
    have h := hp.sym 0 (by omega)
    rw [show m - 1 - 0 = m - 1 by omega] at h
    exact h.symm
  have hbnd : dgt p 0 = 2 ∧ crry p 1 = 1 ∧ crry p m = 1 := by
    have h91 : dgt p 0 ≤ 9 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
    by_cases hm1 : m = 1
    · subst hm1
      have h2 : dgt p 0 = 2 := by omega
      rw [h2] at e0
      have hc : crry p 1 = 1 := by omega
      exact ⟨h2, hc, hc⟩
    · have hcm1 : crry p (m - 1) = crry p 1 := hconst (m - 1) (by omega) (by omega)
      have em := crry_succ p (m - 1)
      rw [show m - 1 + 1 = m by omega, ham1, hcm1] at em
      have hcm4 : crry p m ≤ 4 := crry_le p m
      have hc14 : crry p 1 ≤ 4 := crry_le p 1
      refine ⟨?_, ?_, ?_⟩ <;> omega
  obtain ⟨-, hv1, hvm⟩ := hbnd
  intro j hj
  rcases eq_or_lt_of_le hj with hjm | hjm
  · rw [hjm]; exact hvm
  · by_cases hj0 : j = 0
    · subst hj0; exact crry_zero p
    · rw [hconst j (by omega) (by omega)]; exact hv1

/-- **A083834 C1**: digits of `q = 5p+1` lie in `{0,1,5,6}`. -/
theorem A083834_C1 {p m m' : ℕ} (hp : IsPal p m) (hq : IsPal (5 * p + 1) m')
    (hm : 1 ≤ m) :
    ∀ j < m', dgt (5 * p + 1) j = 0 ∨ dgt (5 * p + 1) j = 1 ∨
      dgt (5 * p + 1) j = 5 ∨ dgt (5 * p + 1) j = 6 := by
  rcases mp_cases hp hq hm with h | h
  · subst h
    obtain ⟨d1, d2⟩ := same_case_digits hp hq hm
    have hc1 := same_case_c1 hp hq hm
    intro j hj
    rw [qdgt]
    by_cases hjev : j % 2 = 0
    · obtain ⟨k, hk⟩ : ∃ k, j = 2 * k := ⟨j / 2, by omega⟩
      have cj : crry p j = 1 := by
        rw [hk]; exact carry_even_same hp hq k (by omega)
      have haj : dgt p j = 0 ∨ dgt p j = 1 := by
        have := d1 j hj hjev; omega
      rw [cj]
      rcases haj with h0 | h1
      · rw [h0]; decide
      · rw [h1]; decide
    · have hod : j % 2 = 1 := by omega
      obtain ⟨k, hk⟩ : ∃ k, j = 2 * k + 1 := ⟨(j - 1) / 2, by omega⟩
      have cj : crry p j = 0 := by
        rw [hk]
        rw [carry_odd_same hp hq k (by omega)]
        exact hc1
      have haj : dgt p j = 2 ∨ dgt p j = 3 := by
        have := d2 j hj hod; omega
      rw [cj]
      rcases haj with h2 | h3
      · rw [h2]; decide
      · rw [h3]; decide
  · subst h
    have hcarry := succ_case_carry hp hq hm
    have hall2 := succ_case_all2 hp hq hm
    intro j hj
    rw [qdgt]
    have cj : crry p j = 1 := hcarry j (by omega)
    rw [cj]
    by_cases hjm : j = m
    · have haj : dgt p j = 0 := by rw [hjm]; exact dgt_eq_zero_of_ge hp.hi le_rfl
      rw [haj]; decide
    · have haj : dgt p j = 2 := hall2 j (by omega)
      rw [haj]; decide

/-- **A083834 C2**: an even-length term is the repunit `1^{m'}`. -/
theorem A083834_C2 {p m m' : ℕ} (hp : IsPal p m) (hq : IsPal (5 * p + 1) m')
    (hm : 1 ≤ m) (hm'e : m' % 2 = 0) : ∀ j < m', dgt (5 * p + 1) j = 1 := by
  rcases mp_cases hp hq hm with h | h
  · subst h
    obtain ⟨hodd, _⟩ := same_case_odd_a0 hp hq hm
    rw [Nat.odd_iff] at hodd
    omega
  · subst h
    have hcarry := succ_case_carry hp hq hm
    have hall2 := succ_case_all2 hp hq hm
    intro j hj
    rw [qdgt]
    have cj : crry p j = 1 := hcarry j (by omega)
    rw [cj]
    by_cases hjm : j = m
    · have haj : dgt p j = 0 := by rw [hjm]; exact dgt_eq_zero_of_ge hp.hi le_rfl
      rw [haj]
    · have haj : dgt p j = 2 := hall2 j (by omega)
      rw [haj]

/-- Backward direction, same-length branch: an odd-length palindrome
with alternating digit classes `a_j ≤ 1` (even positions) /
`a_j ∈ {2,3}` (odd positions) gives a palindrome `5p+1` of
length `m`. -/
theorem alt_gives_pal {p m : ℕ} (hp : IsPal p m) (_hm : 1 ≤ m)
    (hodd : m % 2 = 1)
    (hev : ∀ j, j < m → j % 2 = 0 → dgt p j ≤ 1)
    (hod : ∀ j, j < m → j % 2 = 1 → 2 ≤ dgt p j ∧ dgt p j ≤ 3) :
    IsPal (5 * p + 1) m := by
  -- alternating carry chain: c_j = 1 (j even), c_j = 0 (j odd), j ≤ m
  have hcar : ∀ j, j ≤ m →
      (j % 2 = 0 → crry p j = 1) ∧ (j % 2 = 1 → crry p j = 0) := by
    intro j
    induction j with
    | zero =>
      intro _
      exact ⟨fun _ => crry_zero p, fun h => by omega⟩
    | succ j ih =>
      intro hjm
      obtain ⟨ih0, ih1⟩ := ih (by omega)
      have e := crry_succ p j
      by_cases hjp : j % 2 = 0
      · rw [ih0 hjp] at e
        have haj := hev j (by omega) hjp
        exact ⟨fun h => by omega, fun _ => by omega⟩
      · have hjp' : j % 2 = 1 := by omega
        rw [ih1 hjp'] at e
        have haj := hod j (by omega) hjp'
        exact ⟨fun _ => by omega, fun h => by omega⟩
  refine ⟨?_, ?_, ?_⟩
  · -- sym: ∀ j < m, q_j = q_{m-1-j} (same-parity carries)
    intro j hj
    rw [qdgt, qdgt]
    have ha : dgt p (m - 1 - j) = dgt p j := (hp.sym j hj).symm
    rw [ha]
    have hceq : crry p (m - 1 - j) = crry p j := by
      have hpar : (m - 1 - j) % 2 = j % 2 := by omega
      by_cases hjp : j % 2 = 0
      · have h1 := (hcar j (by omega)).1 hjp
        have h2 := (hcar (m - 1 - j) (by omega)).1 (by omega)
        omega
      · have hjp' : j % 2 = 1 := by omega
        have h1 := (hcar j (by omega)).2 hjp'
        have h2 := (hcar (m - 1 - j) (by omega)).2 (by omega)
        omega
    rw [hceq]
  · -- lo: 10^{m-1} ≤ 5p+1
    have hplo := hp.lo
    omega
  · -- hi: 5p+1 < 10^m via c_m = 0
    have hcm : crry p m = 0 := (hcar m le_rfl).2 hodd
    exact (crry_m_eq_zero_iff hp.hi).mp hcm

end A083833


