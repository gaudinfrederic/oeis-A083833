import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# OEIS A083831 - Israel's conjecture on palindromes `p` with `4p+1` palindrome

Statement (OEIS): palindromes `p` such that `4p+1` is also a palindrome.
Robert Israel (Apr 2018), tagged "It appears":
  for `d` even, the only `d`-digit term is `88...8`
  (i.e. every even-length term is the repdigit `8*(10^d-1)/9`).

Mechanism (carry chain, cloned from the `5p+1` development with
multiplier `4`). `a j = (p / 10^j) % 10` little-endian digits, `m` the
digit length. Closed-form carry `c j = (4 * (p % 10^j) + 1) / 10^j`
(`c 0 = 1` folds the `+1`, `c j ≤ 3`). Then
`q j = ((4p+1) / 10^j) % 10 = (4 a j + c j) % 10` and
`c (j+1) = (4 a j + c j) / 10`. With `q = 4p+1` palindromic of length
`m' ∈ {m, m+1}`:

* `m' = m`  ⟹ carry chain symmetric `c j = c (m-1-j)`, hence 2-periodic
  (`c (j+1) = c (j-1)`), forcing `m` odd, `a 0 ∈ {1,2}`, and
  `a j ∈ {0,1,2}` (`j` even) / `a j ∈ {3,4}` (`j` odd).
* `m' = m+1` ⟹ `c (m-j) = c j`; the swap `g(u,a)=w ∧ g(w,a)=u` with
  `u≠w` is impossible (`11·|u-w| ≤ 9`), so the chain is constant
  `c j = 3` for `1 ≤ j ≤ m`; boundary `4a_0+1 = 33` forces `a_0 = 8`,
  and `4a+3` injective on `[30,39]` propagates `a_j = 8`,
  hence `p = 88...8`.
-/

namespace A083831

/-- The `j`-th decimal digit of `n` (units = `j = 0`). -/
def dgt (n j : ℕ) : ℕ := n / 10 ^ j % 10

/-- `p` has `m`-digit palindromic decimal expansion: symmetric digits,
`10^(m-1) ≤ p < 10^m`. -/
structure IsPal (p m : ℕ) : Prop where
  sym : ∀ j < m, dgt p j = dgt p (m - 1 - j)
  lo : 10 ^ (m - 1) ≤ p
  hi : p < 10 ^ m

/-- Closed-form carry into position `j` when computing `4p+1`. -/
def crry (p j : ℕ) : ℕ := (4 * (p % 10 ^ j) + 1) / 10 ^ j

theorem crry_zero (p : ℕ) : crry p 0 = 1 := by
  unfold crry
  rw [pow_zero, Nat.mod_one]
  norm_num

theorem crry_le (p j : ℕ) : crry p j ≤ 3 := by
  have h : p % 10 ^ j < 10 ^ j := Nat.mod_lt _ (by positivity)
  have h10 : 0 < 10 ^ j := by positivity
  unfold crry
  have := (Nat.div_lt_iff_lt_mul h10).mpr (show 4 * (p % 10 ^ j) + 1 < 4 * 10 ^ j by omega)
  omega

/-- Core identity: `4p+1 = 10^j * (4 Q + c_j) + r` with `r < 10^j`. -/
theorem decomp (p j : ℕ) :
    4 * p + 1 = 10 ^ j * (4 * (p / 10 ^ j) + crry p j) +
      (4 * (p % 10 ^ j) + 1) % 10 ^ j := by
  have h1 : p = 10 ^ j * (p / 10 ^ j) + p % 10 ^ j := (Nat.div_add_mod p _).symm
  have h2 : 4 * (p % 10 ^ j) + 1 =
      10 ^ j * ((4 * (p % 10 ^ j) + 1) / 10 ^ j) + (4 * (p % 10 ^ j) + 1) % 10 ^ j :=
    (Nat.div_add_mod _ _).symm
  unfold crry
  have e3 : 10 ^ j * (4 * (p / 10 ^ j) + (4 * (p % 10 ^ j) + 1) / 10 ^ j) =
      4 * (10 ^ j * (p / 10 ^ j)) + 10 ^ j * ((4 * (p % 10 ^ j) + 1) / 10 ^ j) := by
    ring
  rw [e3]
  omega

/-- The quotient of `4p+1` by `10^j`. -/
theorem div_ten_pow (p j : ℕ) :
    (4 * p + 1) / 10 ^ j = 4 * (p / 10 ^ j) + crry p j := by
  have h := decomp p j
  have hr : (4 * (p % 10 ^ j) + 1) % 10 ^ j < 10 ^ j :=
    Nat.mod_lt _ (by positivity)
  rw [h]
  refine Nat.div_eq_of_lt_le ?_ ?_
  · have mc : (4 * (p / 10 ^ j) + crry p j) * 10 ^ j =
        10 ^ j * (4 * (p / 10 ^ j) + crry p j) := mul_comm _ _
    omega
  · have e : (4 * (p / 10 ^ j) + crry p j + 1) * 10 ^ j =
        10 ^ j * (4 * (p / 10 ^ j) + crry p j) + 10 ^ j := by ring
    rw [e]; omega

/-- Digits of `4p+1` in terms of digits of `p` and carries. -/
theorem qdgt (p j : ℕ) :
    dgt (4 * p + 1) j = (4 * dgt p j + crry p j) % 10 := by
  unfold dgt
  rw [div_ten_pow]
  have : p / 10 ^ j = 10 * (p / 10 ^ j / 10) + p / 10 ^ j % 10 :=
    (Nat.div_add_mod _ _).symm
  omega

/-- Carry recurrence. -/
theorem crry_succ (p j : ℕ) :
    crry p (j + 1) = (4 * dgt p j + crry p j) / 10 := by
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
  have hr : (4 * (p % 10 ^ j) + 1) % 10 ^ j < 10 ^ j := Nat.mod_lt _ hX
  have hdec : 4 * (p % 10 ^ j) + 1 =
      10 ^ j * ((4 * (p % 10 ^ j) + 1) / 10 ^ j) + (4 * (p % 10 ^ j) + 1) % 10 ^ j :=
    (Nat.div_add_mod _ _).symm
  have e5 : 4 * (p % 10 ^ j + 10 ^ j * (p / 10 ^ j % 10)) + 1 =
      10 ^ j * (4 * (p / 10 ^ j % 10) + (4 * (p % 10 ^ j) + 1) / 10 ^ j) +
      (4 * (p % 10 ^ j) + 1) % 10 ^ j := by
    have e6 : 10 ^ j * (4 * (p / 10 ^ j % 10) + (4 * (p % 10 ^ j) + 1) / 10 ^ j) =
        10 ^ j * (4 * (p / 10 ^ j % 10)) + 10 ^ j * ((4 * (p % 10 ^ j) + 1) / 10 ^ j) := by
      ring
    have e7 : 10 ^ j * (4 * (p / 10 ^ j % 10)) = 4 * (10 ^ j * (p / 10 ^ j % 10)) := by
      ring
    rw [e6]; omega
  rw [e5]
  have hX : (10 : ℕ) ^ (j + 1) = 10 ^ j * 10 := by rw [pow_succ]
  rw [hX]
  refine Nat.div_eq_of_lt_le ?_ ?_
  · have hY : 10 * ((4 * (p / 10 ^ j % 10) + (4 * (p % 10 ^ j) + 1) / 10 ^ j) / 10) ≤
        4 * (p / 10 ^ j % 10) + (4 * (p % 10 ^ j) + 1) / 10 ^ j := by omega
    have e1 : (4 * (p / 10 ^ j % 10) + (4 * (p % 10 ^ j) + 1) / 10 ^ j) / 10 *
        (10 ^ j * 10) = 10 * (10 ^ j *
        ((4 * (p / 10 ^ j % 10) + (4 * (p % 10 ^ j) + 1) / 10 ^ j) / 10)) := by ring
    have e2 : 10 ^ j * (10 * ((4 * (p / 10 ^ j % 10) +
        (4 * (p % 10 ^ j) + 1) / 10 ^ j) / 10)) =
        10 * (10 ^ j * ((4 * (p / 10 ^ j % 10) +
        (4 * (p % 10 ^ j) + 1) / 10 ^ j) / 10)) := by ring
    have e3 : 10 ^ j * (10 * ((4 * (p / 10 ^ j % 10) +
        (4 * (p % 10 ^ j) + 1) / 10 ^ j) / 10)) ≤
        10 ^ j * (4 * (p / 10 ^ j % 10) + (4 * (p % 10 ^ j) + 1) / 10 ^ j) := by
      gcongr
    omega
  · have hYd : 4 * (p / 10 ^ j % 10) + (4 * (p % 10 ^ j) + 1) / 10 ^ j =
        10 * ((4 * (p / 10 ^ j % 10) + (4 * (p % 10 ^ j) + 1) / 10 ^ j) / 10) +
        (4 * (p / 10 ^ j % 10) + (4 * (p % 10 ^ j) + 1) / 10 ^ j) % 10 :=
      (Nat.div_add_mod _ _).symm
    have hY : (4 * (p / 10 ^ j % 10) + (4 * (p % 10 ^ j) + 1) / 10 ^ j) % 10 ≤ 9 := by
      omega
    have e1 : ((4 * (p / 10 ^ j % 10) + (4 * (p % 10 ^ j) + 1) / 10 ^ j) / 10 + 1) *
        (10 ^ j * 10) = 10 * (10 ^ j *
        ((4 * (p / 10 ^ j % 10) + (4 * (p % 10 ^ j) + 1) / 10 ^ j) / 10)) + 10 * 10 ^ j := by
      ring
    have e2 : 10 ^ j * (4 * (p / 10 ^ j % 10) + (4 * (p % 10 ^ j) + 1) / 10 ^ j) =
        10 * (10 ^ j * ((4 * (p / 10 ^ j % 10) + (4 * (p % 10 ^ j) + 1) / 10 ^ j) / 10)) +
        10 ^ j * ((4 * (p / 10 ^ j % 10) + (4 * (p % 10 ^ j) + 1) / 10 ^ j) % 10) := by
      conv_lhs => rw [hYd]
      ring
    have e3 : 10 ^ j * ((4 * (p / 10 ^ j % 10) + (4 * (p % 10 ^ j) + 1) / 10 ^ j) % 10) ≤
        9 * 10 ^ j := by
      rw [mul_comm (10 ^ j) ((4 * (p / 10 ^ j % 10) + (4 * (p % 10 ^ j) + 1) / 10 ^ j) % 10)]
      gcongr
    omega

/-- `dgt` vanishes above the length. -/
theorem dgt_eq_zero_of_ge {p m j : ℕ} (h : p < 10 ^ m) (hj : m ≤ j) : dgt p j = 0 := by
  unfold dgt
  have : p < 10 ^ j := lt_of_lt_of_le h (pow_le_pow_right₀ (by norm_num) hj)
  rw [Nat.div_eq_of_lt this, Nat.zero_mod]

/-- Length of `4p+1` is `m` or `m+1`. -/
theorem mp_cases {p m m' : ℕ} (hp : IsPal p m) (hq : IsPal (4 * p + 1) m')
    (hm : 1 ≤ m) : m' = m ∨ m' = m + 1 := by
  have hphi := hp.hi
  have hplo := hp.lo
  have hqhi := hq.hi
  have hqlo := hq.lo
  have hup : 4 * p + 1 < 10 ^ (m + 1) := by
    calc 4 * p + 1 < 4 * 10 ^ m := by omega
      _ < 10 ^ (m + 1) := by rw [pow_succ']; omega
  have hlo : 10 ^ (m - 1) < 4 * p + 1 := by omega
  have h1 : m' - 1 < m + 1 := by
    by_contra h
    replace h := not_lt.mp h
    have : 10 ^ (m + 1) ≤ 10 ^ (m' - 1) := pow_le_pow_right₀ (by norm_num) h
    omega
  have h2 : m ≤ m' := by
    by_contra h
    replace h := not_le.mp h
    have : m' ≤ m - 1 := by omega
    have : 10 ^ m' ≤ 10 ^ (m - 1) := pow_le_pow_right₀ (by norm_num) this
    omega
  omega

/-- `m' = m` iff the top carry vanishes. -/
theorem crry_m_eq_zero_iff {p m : ℕ} (hp : p < 10 ^ m) :
    crry p m = 0 ↔ 4 * p + 1 < 10 ^ m := by
  unfold crry
  rw [Nat.mod_eq_of_lt hp, Nat.div_eq_zero_iff,
      or_iff_right (pow_ne_zero _ (by norm_num) : (10 : ℕ) ^ m ≠ 0)]

/-- Carry symmetry, same-length case: `c_j = c_{m-1-j}`. -/
theorem crry_sym_same {p m : ℕ} (hp : IsPal p m) (hq : IsPal (4 * p + 1) m)
    {j : ℕ} (hj : j < m) : crry p j = crry p (m - 1 - j) := by
  have e := hq.sym j (by omega)
  rw [qdgt, qdgt] at e
  have ha : dgt p (m - 1 - j) = dgt p j := (hp.sym j hj).symm
  rw [ha] at e
  have c1 := crry_le p j
  have c2 := crry_le p (m - 1 - j)
  omega

/-- Length+1 case: the mirrored carry `c_{m-j}` is the forward recurrence
of the same digit `a_j` (palindrome: `a_{m-j-1} = a_j`). This is the k=4
substitute for the k=5 carry symmetry (which fails: `c_{m-j} - c_j` may be
`±2` since `4` does not separate carries mod `10`). -/
theorem crry_mirror {p m : ℕ} (hp : IsPal p m)
    (hm : 1 ≤ m) (j : ℕ) (hj : j ≤ m - 1) :
    crry p (m - j) = (4 * dgt p j + crry p (m - j - 1)) / 10 := by
  have e := crry_succ p (m - j - 1)
  rw [show m - j - 1 + 1 = m - j by omega] at e
  have hpd : dgt p (m - j - 1) = dgt p j := by
    have h := hp.sym j (by omega : j < m)
    rw [show m - 1 - j = m - j - 1 by omega] at h
    exact h.symm
  rw [hpd] at e
  exact e

/-- Output symmetry, length+1 case, raw form:
`(4a_j + c_j) % 10 = (4a_{j-1} + c_{m-j}) % 10` for `1 ≤ j ≤ m-1`. -/
theorem qdgt_sym_succ {p m : ℕ} (hp : IsPal p m) (hq : IsPal (4 * p + 1) (m + 1))
    {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ m - 1) :
    (4 * dgt p j + crry p j) % 10 = (4 * dgt p (j - 1) + crry p (m - j)) % 10 := by
  have e := hq.sym j (by omega)
  have hm_j : m + 1 - 1 - j = m - j := by omega
  rw [hm_j, qdgt, qdgt] at e
  have ha : dgt p (m - j) = dgt p (j - 1) := by
    have h := hp.sym (j - 1) (by omega)
    rw [show m - 1 - (j - 1) = m - j by omega] at h
    exact h.symm
  rw [ha] at e
  exact e

/-- Length+1 case: `q`'s top two digits `10·b_m + b_{m-1}` equal
`4·a_{m-1} + c_{m-1}` (the carry into the top block). -/
theorem top_two_eq {p m : ℕ} (hp : IsPal p m) (hq : IsPal (4 * p + 1) (m + 1))
    (hm : 2 ≤ m) :
    10 * dgt (4 * p + 1) m + dgt (4 * p + 1) (m - 1) =
      4 * dgt p (m - 1) + crry p (m - 1) := by
  have hdiv := div_ten_pow p (m - 1)
  have hdp : p / 10 ^ (m - 1) = dgt p (m - 1) := by
    have hlt : p / 10 ^ (m - 1) < 10 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      have e : (10 : ℕ) ^ m = 10 * 10 ^ (m - 1) := by
        rw [← pow_succ', show m - 1 + 1 = m by omega]
      have hphi := hp.hi
      omega
    unfold dgt
    omega
  have hqm : (4 * p + 1) / 10 ^ m = dgt (4 * p + 1) m := by
    have hlt : (4 * p + 1) / 10 ^ m < 10 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      have e : (10 : ℕ) ^ (m + 1) = 10 * 10 ^ m := by rw [pow_succ']
      have hqhi := hq.hi
      omega
    unfold dgt
    rw [Nat.mod_eq_of_lt hlt]
  have hX : (4 * p + 1) / 10 ^ (m - 1) =
      10 * ((4 * p + 1) / 10 ^ m) + (4 * p + 1) / 10 ^ (m - 1) % 10 := by
    have e := Nat.div_add_mod ((4 * p + 1) / 10 ^ (m - 1)) 10
    have hpow : (10 : ℕ) ^ (m - 1) * 10 = 10 ^ m := by
      have h : (10 : ℕ) ^ (m - 1 + 1) = 10 ^ (m - 1) * 10 := Nat.pow_succ _ _
      rw [show m - 1 + 1 = m by omega] at h
      exact h.symm
    rw [Nat.div_div_eq_div_mul, hpow] at e
    omega
  rw [hqm] at hX
  unfold dgt at hX hdp ⊢
  omega

/-- Same-length case: 2-periodicity `c_{j+1} = c_{j-1}` for `1 ≤ j ≤ m-2`. -/
theorem carry_period_same {p m : ℕ} (hp : IsPal p m) (hq : IsPal (4 * p + 1) m)
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
theorem carry_even_same {p m : ℕ} (hp : IsPal p m) (hq : IsPal (4 * p + 1) m) :
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
theorem carry_odd_same {p m : ℕ} (hp : IsPal p m) (hq : IsPal (4 * p + 1) m) :
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

/-- Same-length case: `m` must be odd and `a_0 ∈ {1,2}`. -/
theorem same_case_odd_a0 {p m : ℕ} (hp : IsPal p m) (hq : IsPal (4 * p + 1) m)
    (hm : 1 ≤ m) : Odd m ∧ 1 ≤ dgt p 0 ∧ dgt p 0 ≤ 2 := by
  have hcm0 : crry p m = 0 := by
    rw [crry_m_eq_zero_iff hp.hi]; exact hq.hi
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
    have codd := carry_odd_same hp hq (k - 1) (by omega)
    rw [show 2 * (k - 1) + 1 = m - 1 by omega] at codd
    have hc1 : crry p 1 = 1 := by rw [← csym] at codd; exact codd.symm
    have e1 : crry p 1 = (4 * dgt p 0 + 1) / 10 := by
      have e := crry_succ p 0
      rw [crry_zero] at e
      exact e
    have em := crry_succ p (m - 1)
    have hsym2 : crry p (m - 1) = 1 := csym.symm
    rw [show m - 1 + 1 = m by omega, ← htop0, hsym2] at em
    -- em : c_m = (4 a_0 + 1)/10 = 1 ≠ 0 = hcm0
    exfalso
    omega
  · -- m odd: a_0 ≤ 2
    refine ⟨Nat.odd_iff.mpr (by omega), ?_, ?_⟩
    · rw [htop0]; exact htop
    · have hmk : m - 1 = 2 * ((m - 1) / 2) := by omega
      have ceven := carry_even_same hp hq ((m - 1) / 2) (by omega)
      rw [← hmk] at ceven
      have em := crry_succ p (m - 1)
      rw [show m - 1 + 1 = m by omega, ← htop0, ceven, hcm0] at em
      -- em : 0 = (4 a_0 + 1)/10 → a_0 ≤ 2
      omega

/-- Same-length case: digit classes. -/
theorem same_case_digits {p m : ℕ} (hp : IsPal p m) (hq : IsPal (4 * p + 1) m)
    (hm : 1 ≤ m) :
    (∀ j, j < m → j % 2 = 0 → dgt p j ≤ 2) ∧
    (∀ j, j < m → j % 2 = 1 → 3 ≤ dgt p j ∧ dgt p j ≤ 4) := by
  obtain ⟨hmo, ha0lo, ha0hi⟩ := same_case_odd_a0 hp hq hm
  have hcm0 : crry p m = 0 := by
    rw [crry_m_eq_zero_iff hp.hi]; exact hq.hi
  have hc1 : crry p 1 = 0 := by
    have e : crry p 1 = (4 * dgt p 0 + 1) / 10 := by
      have e := crry_succ p 0
      rw [crry_zero] at e
      exact e
    omega
  refine ⟨?_, ?_⟩
  · intro j hj hev
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
    have hjm : j + 1 ≤ m - 1 := by
      obtain ⟨t, ht⟩ := hmo
      omega
    have cj1 : crry p (j + 1) = 1 := by
      have hje : j + 1 = 2 * ((j + 1) / 2) := by omega
      rw [hje]
      exact carry_even_same hp hq ((j + 1) / 2) (by omega)
    rw [cj1] at e
    unfold dgt at e ⊢
    refine ⟨?_, ?_⟩ <;> omega

/-- Length+1 case: every digit is `8`. -/
theorem succ_case_chain {p m : ℕ} (hp : IsPal p m) (hq : IsPal (4 * p + 1) (m + 1))
    (hm : 1 ≤ m) : ∀ j, j ≤ m - 1 → dgt p j = 8 ∧ crry p (j + 1) = 3 := by
  -- boundary: b_0 = b_m  →  (4 a_0 + 1) % 10 = c_m
  have hb := hq.sym 0 (by omega : 0 < m + 1)
  rw [show m + 1 - 1 - 0 = m by omega, qdgt, qdgt, crry_zero] at hb
  have hdm0 : dgt p m = 0 := dgt_eq_zero_of_ge hp.hi le_rfl
  rw [hdm0] at hb
  have hcm3 : crry p m ≤ 3 := crry_le p m
  have hb2 : (4 * dgt p 0 + 1) % 10 = crry p m := by omega
  have htop : 1 ≤ dgt p 0 := by
    have h1 : 1 ≤ p / 10 ^ (m - 1) := Nat.div_pos hp.lo (by positivity)
    have h2 : p / 10 ^ (m - 1) < 10 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity : (0:ℕ) < 10 ^ (m - 1))]
      have e : (10 : ℕ) ^ m = 10 * 10 ^ (m - 1) := by
        rw [← pow_succ', show m - 1 + 1 = m by omega]
      have hphi := hp.hi
      omega
    have hd : dgt p (m - 1) = p / 10 ^ (m - 1) := by unfold dgt; omega
    have h := hp.sym 0 (by omega : 0 < m)
    rw [show m - 1 - 0 = m - 1 by omega] at h
    omega
  -- a_0 = 8 : boundary + top-two-digit equation
  have ha0 : dgt p 0 = 8 := by
    by_cases hm1 : m = 1
    · subst hm1
      have e : crry p 1 = (4 * dgt p 0 + 1) / 10 := by
        have e := crry_succ p 0
        rw [crry_zero] at e
        exact e
      have h91 : dgt p 0 ≤ 9 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
      omega
    · have ham1 : dgt p (m - 1) = dgt p 0 := by
        have h := hp.sym 0 (by omega : 0 < m)
        rw [show m - 1 - 0 = m - 1 by omega] at h
        exact h.symm
      have ec := crry_succ p (m - 1)
      rw [show m - 1 + 1 = m by omega, ham1] at ec
      have hcm1 : crry p (m - 1) ≤ 3 := crry_le p (m - 1)
      have h91 : dgt p 0 ≤ 9 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
      interval_cases dgt p 0 <;> omega
  -- joint induction: (A) mirror congruence + (B) mirrored recurrence on a_j
  have hprop : ∀ j, j ≤ m - 1 → dgt p j = 8 ∧ crry p (j + 1) = 3 := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨ha0, ?_⟩
      have e : crry p 1 = (4 * dgt p 0 + 1) / 10 := by
        have e := crry_succ p 0
        rw [crry_zero] at e
        exact e
      rw [ha0] at e
      omega
    | succ j ih =>
      intro hj
      obtain ⟨haj, hcj⟩ := ih (by omega)
      -- (A): (4·a_{j+1} + 3) % 10 = (32 + c_{m-j-1}) % 10
      have eA := qdgt_sym_succ hp hq (j := j + 1) (by omega) (by omega)
      rw [show j + 1 - 1 = j by omega, haj, hcj] at eA
      -- (B): c_{m-j-1} = (4·a_{j+1} + c_{m-j-2}) / 10
      have eB := crry_mirror hp hm (j + 1) (by omega)
      have hc1 : crry p (m - (j + 1)) ≤ 3 := crry_le p _
      have hc2 : crry p (m - (j + 1) - 1) ≤ 3 := crry_le p _
      have ha9 : dgt p (j + 1) ≤ 9 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
      have hX3 : crry p (m - (j + 1)) = 3 := by omega
      have haj1 : dgt p (j + 1) = 8 := by omega
      have e2 := crry_succ p (j + 1)
      rw [haj1, hcj] at e2
      exact ⟨haj1, by omega⟩
  intro j hj
  exact hprop j hj

/-- Length+1 case: every digit is `8`. -/
theorem succ_case_all8 {p m : ℕ} (hp : IsPal p m) (hq : IsPal (4 * p + 1) (m + 1))
    (hm : 1 ≤ m) : ∀ j < m, dgt p j = 8 := by
  intro j hj
  exact (succ_case_chain hp hq hm j (by omega)).1

/-- **Israel's conjecture (A083831)**: for `m` even, every digit of `p`
is `8` (`p = 88...8`). -/
theorem A083831_even {p m m' : ℕ} (hp : IsPal p m) (hq : IsPal (4 * p + 1) m')
    (hm : 1 ≤ m) (hme : m % 2 = 0) : ∀ j < m, dgt p j = 8 := by
  rcases mp_cases hp hq hm with h | h
  · subst h
    obtain ⟨hodd, _, _⟩ := same_case_odd_a0 hp hq hm
    rw [Nat.odd_iff] at hodd
    omega
  · subst h
    exact succ_case_all8 hp hq hm

/-- Bonus (digit alphabet): every digit of `p` is `≤ 4` or `= 8`. -/
theorem A083831_digits {p m m' : ℕ} (hp : IsPal p m) (hq : IsPal (4 * p + 1) m')
    (hm : 1 ≤ m) : ∀ j < m, dgt p j ≤ 4 ∨ dgt p j = 8 := by
  rcases mp_cases hp hq hm with h | h
  · subst h
    have ⟨d1, d2⟩ := same_case_digits hp hq hm
    intro j hj
    by_cases hjev : j % 2 = 0
    · exact Or.inl (le_trans (d1 j hj hjev) (by norm_num))
    · have hod : j % 2 = 1 := by omega
      exact Or.inl (d2 j hj hod).2
  · subst h
    intro j hj
    exact Or.inr (succ_case_all8 hp hq hm j hj)

/-- Same-length case: `c_1 = 0`. -/
theorem same_case_c1 {p m : ℕ} (hp : IsPal p m) (hq : IsPal (4 * p + 1) m)
    (hm : 1 ≤ m) : crry p 1 = 0 := by
  obtain ⟨_, ha0lo, ha0hi⟩ := same_case_odd_a0 hp hq hm
  have e : crry p 1 = (4 * dgt p 0 + 1) / 10 := by
    have e := crry_succ p 0
    rw [crry_zero] at e
    exact e
  omega

/-- Length+1 case: the carry chain equals `3` for `1 ≤ j ≤ m`. -/
theorem succ_case_carry {p m : ℕ} (hp : IsPal p m) (hq : IsPal (4 * p + 1) (m + 1))
    (hm : 1 ≤ m) : ∀ j, 1 ≤ j → j ≤ m → crry p j = 3 := by
  intro j hj1 hjm
  have h := (succ_case_chain hp hq hm (j - 1) (by omega)).2
  rw [show j - 1 + 1 = j by omega] at h
  exact h

/-- **A083832** (companion, digit alphabet of the image): digits of
`q = 4p+1` lie in `{1,2,3,5,6,9}`. -/
theorem A083832_digits {p m m' : ℕ} (hp : IsPal p m) (hq : IsPal (4 * p + 1) m')
    (hm : 1 ≤ m) :
    ∀ j < m', dgt (4 * p + 1) j = 1 ∨ dgt (4 * p + 1) j = 2 ∨
      dgt (4 * p + 1) j = 3 ∨ dgt (4 * p + 1) j = 5 ∨
      dgt (4 * p + 1) j = 6 ∨ dgt (4 * p + 1) j = 9 := by
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
      have haj : dgt p j ≤ 2 := d1 j hj hjev
      rw [cj]
      rcases (by omega : dgt p j = 0 ∨ dgt p j = 1 ∨ dgt p j = 2) with
        h0 | h1 | h2
      · rw [h0]; decide
      · rw [h1]; decide
      · rw [h2]; decide
    · have hod : j % 2 = 1 := by omega
      obtain ⟨k, hk⟩ : ∃ k, j = 2 * k + 1 := ⟨(j - 1) / 2, by omega⟩
      have cj : crry p j = 0 := by
        rw [hk]
        rw [carry_odd_same hp hq k (by omega)]
        exact hc1
      have haj : 3 ≤ dgt p j ∧ dgt p j ≤ 4 := d2 j hj hod
      rw [cj]
      rcases (by omega : dgt p j = 3 ∨ dgt p j = 4) with h3 | h4
      · rw [h3]; decide
      · rw [h4]; decide
  · subst h
    have hcarry := succ_case_carry hp hq hm
    have hall8 := succ_case_all8 hp hq hm
    intro j hj
    rw [qdgt]
    by_cases hj0 : j = 0
    · subst hj0
      rw [crry_zero, hall8 0 (by omega)]
      decide
    · by_cases hjm : j = m
      · rw [hjm, show dgt p m = 0 from dgt_eq_zero_of_ge hp.hi le_rfl,
            hcarry m (by omega) le_rfl]
        decide
      · rw [hcarry j (by omega) (by omega), hall8 j (by omega)]
        decide

/-- Backward direction, same-length branch: an odd-length palindrome
with alternating digit classes `a_j ≤ 2` (even positions) /
`a_j ∈ {3,4}` (odd positions) gives a palindrome `4p+1` of
length `m`. -/
theorem alt_gives_pal {p m : ℕ} (hp : IsPal p m) (_hm : 1 ≤ m)
    (hodd : m % 2 = 1)
    (hev : ∀ j, j < m → j % 2 = 0 → dgt p j ≤ 2)
    (hod : ∀ j, j < m → j % 2 = 1 → 3 ≤ dgt p j ∧ dgt p j ≤ 4) :
    IsPal (4 * p + 1) m := by
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
  · -- lo: 10^{m-1} ≤ 4p+1
    have hplo := hp.lo
    omega
  · -- hi: 4p+1 < 10^m via c_m = 0
    have hcm : crry p m = 0 := (hcar m le_rfl).2 hodd
    exact (crry_m_eq_zero_iff hp.hi).mp hcm

end A083831
