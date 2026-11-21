import A083833
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A083837 - les zéros affichés de la fiche OEIS rendus inconditionnels

`A083837(k)` = plus petit palindrome `n` tel que `k·n+1` est palindrome,
ou `0` si aucun n'existe. La fiche affiche `0` aux positions
`k ∈ {12,17,23,31,37,41,42,48,51,53,61,64,71,74,79,81,86,91,96,101,103}`
avec le commentaire de Ray Chandler (13 juil. 2003) :
« 0 in sequence indicates no palindrome < 10^15 » - borne de recherche,
pas une preuve. Ce module transforme ces 21 zéros affichés en théorèmes
d'inexistence universelle.

**Obstruction de bord.** Soient `p` palindrome à `m` chiffres de
préfixe-`w` `P` (les `w` premiers chiffres) et `q = k·p+1` palindrome à
`m'` chiffres. Alors :

* `q ∈ (k·P·10^{m-w}, k·(P+1)·10^{m-w}]` (encadrement par le préfixe) ;
* le préfixe-`w` `L` de `q` vaut `revW w (k·revW w P + 1)` : les `w`
  derniers chiffres de `q` sont le renversé du préfixe-`w` de `p`, et le
  préfixe-`w` de `q` est le renversé des `w` derniers de `q` ;
* avec `s = m' - m ∈ [0, S]` (`S` borné par `k < 10^S` car `q < k·10^m`),
  la rencontre des deux intervalles impose
  `L·10^s ≤ k·(P+1)` et `k·P < (L+1)·10^s`.

Le prédicat booléen `okP k w S P` teste cette obstruction ; la liste
`escapesIn k w S cand` retient les préfixes qui y échappent. Arbre de
certificats (vérifié par énumération : aucun témoin `< 10^11`) :

* profondeur 1 (`escapesIn k 1 2 [1..9] = ∅`) :
  `12, 31, 37, 41, 42, 51, 53, 61, 64, 71, 81, 86, 91, 96` ;
* profondeur 2 (échappées de niveau 1 tuées par `m = 1`, niveau 2 vide) :
  `17 (E1={2}), 23 (E1={1}), 74 (E1={6,9}), 101 (E1={1..8}, S=3),
  103 (E1={5}, S=3)` ;
* profondeur 3 : `48 (E1={1}, E2={19}, E3=∅)`,
  `79 (E1={6}, E2={65}, E3=∅)`.
-/

open A083833

namespace A083837

/-- Renversé des `w` derniers chiffres de `n` : `revW w n` lit les
chiffres `w-1, …, 0` et les remet en ordre inverse. Seuls les `w`
derniers chiffres comptent (identique sur `n % 10^w`). -/
def revW : ℕ → ℕ → ℕ
  | 0, _ => 0
  | w + 1, n => dgt n w + 10 * revW w n

/-- Certificat d'obstruction pour un préfixe-`w` `P` de `p` :
`L = revW w (k·revW w P + 1)` est le préfixe-`w` qu'exigerait
`q = k·p+1` palindrome ; `okP = true` ssi `L < 10^{w-1}` (préfixe
impossible, `q` finirait par `0`) ou aucun `s ≤ S` ne satisfait la
condition de recouvrement `L·10^s ≤ k·(P+1) ∧ k·P < (L+1)·10^s`. -/
def okP (k w S P : ℕ) : Bool :=
  decide (revW w (k * revW w P + 1) < 10 ^ (w - 1) ∨
    ∀ s : ℕ, s < S + 1 → (k * (P + 1) < revW w (k * revW w P + 1) * 10 ^ s ∨
      (revW w (k * revW w P + 1) + 1) * 10 ^ s ≤ k * P))

/-- Préfixes de `cand` échappant à l'obstruction `okP`. -/
def escapesIn (k w S : ℕ) (cand : List ℕ) : List ℕ :=
  cand.filter fun P => !(okP k w S P)

/-- `dgt n j` est un chiffre décimal. -/
theorem dgt_lt (n j : ℕ) : dgt n j < 10 := Nat.mod_lt _ (by norm_num)

/-- Multiplication à gauche croissante sur `ℕ`. -/
theorem mmul_l {a b : ℕ} (h : a ≤ b) (c : ℕ) : c * a ≤ c * b := by
  gcongr

/-- Multiplication à droite croissante sur `ℕ`. -/
theorem mmul_r {a b : ℕ} (h : a ≤ b) (c : ℕ) : a * c ≤ b * c := by
  rw [mul_comm a c, mul_comm b c]
  exact mmul_l h c

/-- Un palindrome a une longueur `≥ 1`. -/
theorem pal_one_le {n l : ℕ} (hn : IsPal n l) : 1 ≤ l := by
  by_contra h
  have hl : l = 0 := by omega
  subst hl
  have hlo := hn.lo
  have hhi := hn.hi
  norm_num at hlo hhi
  omega

/-- `decide p = false` dès que `¬p`. -/
theorem decide_false {P : Prop} [Decidable P] (h : ¬P) : decide P = false := by
  cases hP : decide P
  · rfl
  · exact absurd (of_decide_eq_true hP) h

/-- `b ≠ true` implique `b = false`. -/
theorem bool_eq_false {b : Bool} (h : b ≠ true) : b = false := by
  cases b <;> simp_all

/-- Tronçon de poids fort du reste : `n % 10^{w+1}` se décompose. -/
theorem mod_succ (n w : ℕ) : n % 10 ^ (w + 1) = n % 10 ^ w + dgt n w * 10 ^ w := by
  have h1 := Nat.div_add_mod n (10 ^ (w + 1))
  have h2 := Nat.div_add_mod n (10 ^ w)
  have hC : n / 10 ^ w = 10 * (n / 10 ^ (w + 1)) + dgt n w := by
    have e : n / 10 ^ w = 10 * (n / 10 ^ w / 10) + n / 10 ^ w % 10 :=
      (Nat.div_add_mod _ _).symm
    have e2 : n / 10 ^ w / 10 = n / 10 ^ (w + 1) := by
      rw [Nat.div_div_eq_div_mul, ← pow_succ]
    rw [e2] at e
    unfold dgt
    exact e
  have h3 : 10 ^ w * (n / 10 ^ w) =
      10 ^ (w + 1) * (n / 10 ^ (w + 1)) + dgt n w * 10 ^ w := by
    rw [hC]
    have e : 10 ^ w * (10 * (n / 10 ^ (w + 1)) + dgt n w) =
        10 ^ (w + 1) * (n / 10 ^ (w + 1)) + dgt n w * 10 ^ w := by
      rw [mul_add, ← mul_assoc, ← pow_succ, mul_comm (10 ^ w) (dgt n w)]
    rw [e]
  rw [h3] at h2
  omega

/-- Décomposition petite-boutiste : `n % 10^w` est la somme de ses `w`
derniers chiffres. -/
theorem lowW (n w : ℕ) : n % 10 ^ w = ∑ j ∈ Finset.range w, dgt n j * 10 ^ j := by
  induction w with
  | zero => rw [Finset.range_zero, Finset.sum_empty, pow_zero]; exact Nat.mod_one n
  | succ w ih =>
    rw [Finset.sum_range_succ, ← ih]
    exact mod_succ n w

/-- `dgt` d'un quotient par `10^a`. -/
theorem dgt_div_shift (x a t : ℕ) : dgt (x / 10 ^ a) t = dgt x (t + a) := by
  unfold dgt
  rw [Nat.div_div_eq_div_mul, ← pow_add, add_comm a t]

/-- `revW` sous forme de somme explicite. -/
theorem revW_eq (w n : ℕ) :
    revW w n = ∑ j ∈ Finset.range w, dgt n (w - 1 - j) * 10 ^ j := by
  induction w with
  | zero => simp [revW]
  | succ w ih =>
    have hdef : revW (w + 1) n = dgt n w + 10 * revW w n := rfl
    rw [hdef, ih, Finset.sum_range_succ', Finset.mul_sum]
    have h0 : dgt n (w + 1 - 1 - 0) * 10 ^ 0 = dgt n w := by simp
    rw [h0]
    have hs : ∑ i ∈ Finset.range w, 10 * (dgt n (w - 1 - i) * 10 ^ i) =
        ∑ k ∈ Finset.range w, dgt n (w + 1 - 1 - (k + 1)) * 10 ^ (k + 1) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      have e1 : w + 1 - 1 - (j + 1) = w - 1 - j := by omega
      rw [e1, pow_succ]
      ring
    rw [hs]
    exact Nat.add_comm _ _

/-- Palindrome : les `w` derniers chiffres de `n` sont le renversé de
son préfixe-`w`. -/
theorem low_rev {n l w : ℕ} (hn : IsPal n l) (hw : w ≤ l) :
    n % 10 ^ w = revW w (n / 10 ^ (l - w)) := by
  rw [revW_eq, lowW]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  have h1 : dgt n j = dgt n (l - 1 - j) := hn.sym j (by omega)
  have h2 : dgt (n / 10 ^ (l - w)) (w - 1 - j) = dgt n (l - 1 - j) := by
    rw [dgt_div_shift]
    congr 1
    omega
  rw [h1, h2]

/-- Extraction : le chiffre `t` d'une somme à chiffres séparés est le
poids `a t`, pourvu que tous les poids soient `< 10`. -/
theorem dgt_sum_low {a : ℕ → ℕ} {w : ℕ} (ha : ∀ i < w, a i < 10) {t : ℕ}
    (ht : t < w) : dgt (∑ i ∈ Finset.range w, a i * 10 ^ i) t = a t := by
  have hgeom : ∀ n : ℕ, (∑ i ∈ Finset.range n, 9 * 10 ^ i) = 10 ^ n - 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have e : 10 ^ (n + 1) = 10 * 10 ^ n := by rw [pow_succ']
      rw [e]
      have h10 : 0 < 10 ^ n := by positivity
      omega
  have hsplit : ∑ i ∈ Finset.range w, a i * 10 ^ i =
      (∑ i ∈ Finset.range (t + 1), a i * 10 ^ i) +
        ∑ j ∈ Finset.range (w - (t + 1)), a (t + 1 + j) * 10 ^ (t + 1 + j) := by
    have e := Finset.sum_range_add (fun i => a i * 10 ^ i) (t + 1) (w - (t + 1))
    rw [show t + 1 + (w - (t + 1)) = w by omega] at e
    exact e
  have htail : ∑ j ∈ Finset.range (w - (t + 1)), a (t + 1 + j) * 10 ^ (t + 1 + j) =
      10 ^ (t + 1) * ∑ j ∈ Finset.range (w - (t + 1)), a (t + 1 + j) * 10 ^ j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_add]
    ring
  have hB : ∑ i ∈ Finset.range t, a i * 10 ^ i < 10 ^ t := by
    have hle : ∑ i ∈ Finset.range t, a i * 10 ^ i ≤
        ∑ i ∈ Finset.range t, 9 * 10 ^ i := by
      apply Finset.sum_le_sum
      intro i hi
      rw [Finset.mem_range] at hi
      have hai : a i ≤ 9 := by have := ha i (by omega); omega
      exact mmul_r hai _
    rw [hgeom] at hle
    have h10 : 0 < 10 ^ t := by positivity
    omega
  have hlow : ∑ i ∈ Finset.range (t + 1), a i * 10 ^ i < 10 ^ (t + 1) := by
    rw [Finset.sum_range_succ]
    have e : 10 ^ (t + 1) = 10 * 10 ^ t := by rw [pow_succ']
    have hat : a t * 10 ^ t ≤ 9 * 10 ^ t :=
      mmul_r (by have := ha t ht; omega) _
    have h10 : 0 < 10 ^ t := by positivity
    omega
  have hform : ∑ i ∈ Finset.range w, a i * 10 ^ i =
      (∑ i ∈ Finset.range t, a i * 10 ^ i) +
        10 ^ t * (a t + 10 * ∑ j ∈ Finset.range (w - (t + 1)),
          a (t + 1 + j) * 10 ^ j) := by
    rw [hsplit, htail, Finset.sum_range_succ]
    have e : a t * 10 ^ t +
        10 ^ (t + 1) * (∑ j ∈ Finset.range (w - (t + 1)), a (t + 1 + j) * 10 ^ j) =
        10 ^ t * (a t + 10 * (∑ j ∈ Finset.range (w - (t + 1)),
          a (t + 1 + j) * 10 ^ j)) := by
      rw [pow_succ']
      ring
    rw [add_assoc, e]
  unfold dgt
  have hpos : (0 : ℕ) < 10 ^ t := by positivity
  rw [hform, Nat.add_mul_div_left _ _ hpos]
  have hB0 : (∑ i ∈ Finset.range t, a i * 10 ^ i) / 10 ^ t = 0 :=
    Nat.div_eq_of_lt hB
  rw [hB0, zero_add, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (ha t ht)

/-- Extraction de chiffre depuis une image `revW`. -/
theorem dgt_revW {w n t : ℕ} (ht : t < w) :
    dgt (revW w n) t = dgt n (w - 1 - t) := by
  rw [revW_eq]
  exact dgt_sum_low (fun i _ => dgt_lt _ _) ht

/-- `revW` est une involution sous `10^w`. -/
theorem revW_invol {w n : ℕ} (hn : n < 10 ^ w) : revW w (revW w n) = n := by
  have e : revW w (revW w n) = ∑ j ∈ Finset.range w, dgt n j * 10 ^ j := by
    rw [revW_eq]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [dgt_revW (by omega : w - 1 - j < w)]
    have hidx : w - 1 - (w - 1 - j) = j := by omega
    rw [hidx]
  rw [e, ← lowW]
  exact Nat.mod_eq_of_lt hn

/-- Les `w` premiers chiffres de `n % 10^w` sont ceux de `n`. -/
theorem dgt_mod {n w t : ℕ} (ht : t < w) : dgt (n % 10 ^ w) t = dgt n t := by
  have hpos : (0 : ℕ) < 10 ^ t := by positivity
  have hT : 10 ^ w = 10 ^ t * 10 ^ (w - t) := by rw [← pow_add]; congr 1; omega
  have hn : n = n % 10 ^ w + 10 ^ t * (n / 10 ^ w * 10 ^ (w - t)) := by
    have h := Nat.div_add_mod n (10 ^ w)
    nth_rewrite 1 [← h]
    nth_rewrite 1 [hT]
    ring
  have hdiv : n / 10 ^ t = n % 10 ^ w / 10 ^ t + n / 10 ^ w * 10 ^ (w - t) := by
    nth_rewrite 1 [hn]
    rw [Nat.add_mul_div_left _ _ hpos]
  unfold dgt
  rw [hdiv]
  have e : n / 10 ^ w * 10 ^ (w - t) = 10 * (n / 10 ^ w * 10 ^ (w - t - 1)) := by
    have h : 10 ^ (w - t) = 10 * 10 ^ (w - t - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [h]
    ring
  rw [e, Nat.add_mul_mod_self_left]

/-- `revW` ne voit que `n % 10^w`. -/
theorem revW_mod (w n : ℕ) : revW w n = revW w (n % 10 ^ w) := by
  rw [revW_eq, revW_eq]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  congr 1
  exact (dgt_mod (by omega : w - 1 - j < w)).symm

/-- Le préfixe-`w` d'un palindrome de longueur `l` vit dans
`[10^{w-1}, 10^w)`. -/
theorem prefix_range {n l w : ℕ} (hn : IsPal n l) (hw : 1 ≤ w) (hwm : w ≤ l) :
    n / 10 ^ (l - w) ∈ List.range' (10 ^ (w - 1)) (10 ^ w - 10 ^ (w - 1)) := by
  have hmod : n % 10 ^ (l - w) < 10 ^ (l - w) := Nat.mod_lt _ (by positivity)
  have hdec := Nat.div_add_mod n (10 ^ (l - w))
  have hdec' : (n / 10 ^ (l - w)) * 10 ^ (l - w) + n % 10 ^ (l - w) = n := by
    rw [mul_comm]; exact hdec
  have hnlo := hn.lo
  have hnhi := hn.hi
  have hPlo : 10 ^ (w - 1) ≤ n / 10 ^ (l - w) := by
    by_contra h
    push Not at h
    have hP1 : n / 10 ^ (l - w) + 1 ≤ 10 ^ (w - 1) := by omega
    have e : 10 ^ (w - 1) * 10 ^ (l - w) = 10 ^ (l - 1) := by
      rw [← pow_add]; congr 1; omega
    have hstep : (n / 10 ^ (l - w) + 1) * 10 ^ (l - w) ≤
        10 ^ (w - 1) * 10 ^ (l - w) := mmul_r hP1 _
    have hexp : (n / 10 ^ (l - w) + 1) * 10 ^ (l - w) =
        (n / 10 ^ (l - w)) * 10 ^ (l - w) + 10 ^ (l - w) := by
      rw [add_mul, one_mul]
    omega
  have hPhi : n / 10 ^ (l - w) < 10 ^ w := by
    by_contra h
    push Not at h
    have h2 : 10 ^ w * 10 ^ (l - w) ≤ (n / 10 ^ (l - w)) * 10 ^ (l - w) :=
      mmul_r h _
    have e2 : 10 ^ w * 10 ^ (l - w) = 10 ^ l := by
      rw [← pow_add]; congr 1; omega
    omega
  have hs : 10 ^ (w - 1) ≤ 10 ^ w :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  exact List.mem_range'.mpr
    ⟨n / 10 ^ (l - w) - 10 ^ (w - 1), by omega, by omega⟩

/-- Le préfixe-`(w+1)` étend le préfixe-`w` d'un chiffre. -/
theorem prefix_ext {p m w : ℕ} (hwm : w + 1 ≤ m) :
    p / 10 ^ (m - (w + 1)) = 10 * (p / 10 ^ (m - w)) + dgt p (m - 1 - w) := by
  have e := Nat.div_add_mod (p / 10 ^ (m - (w + 1))) 10
  have hd : p / 10 ^ (m - (w + 1)) / 10 = p / 10 ^ (m - w) := by
    rw [Nat.div_div_eq_div_mul, ← pow_succ,
      show m - (w + 1) + 1 = m - w by omega]
  rw [hd] at e
  have idx : m - (w + 1) = m - 1 - w := by omega
  rw [← e]
  unfold dgt
  rw [idx]

/-- Longueur exacte d'un palindrome concret. -/
theorem pin_m' {q m' a : ℕ} (hq : IsPal q m') (hlo : 10 ^ (a - 1) ≤ q)
    (hhi : q < 10 ^ a) : m' = a := by
  have hqlo := hq.lo
  have hqhi := hq.hi
  have h1 : m' - 1 < a := by
    by_contra h
    push Not at h
    have : 10 ^ a ≤ 10 ^ (m' - 1) := pow_le_pow_right₀ (by norm_num) h
    omega
  have h2 : a - 1 < m' := by
    by_contra h
    push Not at h
    have : 10 ^ m' ≤ 10 ^ (a - 1) := pow_le_pow_right₀ (by norm_num) h
    omega
  omega

/-- Un palindrome concret dont les chiffres de bord diffèrent est
impossible. -/
theorem not_pal_of {q m' a : ℕ} (hq : IsPal q m') (hlo : 10 ^ (a - 1) ≤ q)
    (hhi : q < 10 ^ a) (hd : dgt q 0 ≠ dgt q (a - 1)) : False := by
  have ha : m' = a := pin_m' hq hlo hhi
  have ha0 : 0 < a := by
    by_contra h0
    have h0' : a = 0 := by omega
    subst h0'
    have hl : (1 : ℕ) ≤ q := hlo
    have hh : q < 1 := hhi
    omega
  have hm' : 0 < m' := by omega
  have hs := hq.sym 0 hm'
  rw [ha] at hs
  exact hd hs

/-- **Obstruction de bord générique** : si `q = k·p+1` est palindrome,
le préfixe-`w` de `p` échappe à `okP`. -/
theorem prefix_escapes {k w S : ℕ} (hk : 2 ≤ k) (hkS : k < 10 ^ S) (hw : 1 ≤ w)
    {p m m' : ℕ} (hp : IsPal p m) (hq : IsPal (k * p + 1) m') (hwm : w ≤ m) :
    okP k w S (p / 10 ^ (m - w)) = false := by
  have hp_lo := hp.lo
  have hp_hi := hp.hi
  have hq_lo := hq.lo
  have hq_hi := hq.hi
  have hpmod : p % 10 ^ (m - w) < 10 ^ (m - w) := Nat.mod_lt _ (by positivity)
  have hpdec := Nat.div_add_mod p (10 ^ (m - w))
  -- hpdec : 10^{m-w}·(p/10^{m-w}) + p%10^{m-w} = p
  have hplo : 10 ^ (m - w) * (p / 10 ^ (m - w)) ≤ p := by omega
  have hphi : p < 10 ^ (m - w) * (p / 10 ^ (m - w) + 1) := by
    rw [mul_add, mul_one]; omega
  have hplo2 : (p / 10 ^ (m - w)) * 10 ^ (m - w) ≤ p := by
    rw [mul_comm]; exact hplo
  have hphi2 : p < (p / 10 ^ (m - w) + 1) * 10 ^ (m - w) := by
    rw [mul_comm]; exact hphi
  have hPlo : 10 ^ (w - 1) ≤ p / 10 ^ (m - w) := by
    by_contra h
    push Not at h
    have hP1 : p / 10 ^ (m - w) + 1 ≤ 10 ^ (w - 1) := by omega
    have e : 10 ^ (w - 1) * 10 ^ (m - w) = 10 ^ (m - 1) := by
      rw [← pow_add]; congr 1; omega
    have h2 : p < 10 ^ (m - 1) := by
      calc p < (p / 10 ^ (m - w) + 1) * 10 ^ (m - w) := hphi2
        _ ≤ 10 ^ (w - 1) * 10 ^ (m - w) := mmul_r hP1 _
        _ = 10 ^ (m - 1) := e
    omega
  have hPhi : p / 10 ^ (m - w) < 10 ^ w := by
    by_contra h
    push Not at h
    have h2 : 10 ^ w * 10 ^ (m - w) ≤ (p / 10 ^ (m - w)) * 10 ^ (m - w) :=
      mmul_r h _
    have e : 10 ^ w * 10 ^ (m - w) = 10 ^ m := by
      rw [← pow_add]; congr 1; omega
    rw [e] at h2
    omega
  have hqlo : k * (p / 10 ^ (m - w)) * 10 ^ (m - w) < k * p + 1 := by
    have h1 : k * ((p / 10 ^ (m - w)) * 10 ^ (m - w)) ≤ k * p :=
      mmul_l hplo2 _
    rw [← mul_assoc] at h1
    omega
  have hqhi : k * p + 1 ≤ k * ((p / 10 ^ (m - w) + 1) * 10 ^ (m - w)) := by
    have h1 : p + 1 ≤ (p / 10 ^ (m - w) + 1) * 10 ^ (m - w) := by
      have he : (p / 10 ^ (m - w) + 1) * 10 ^ (m - w) =
          10 ^ (m - w) * (p / 10 ^ (m - w)) + 10 ^ (m - w) := by ring
      rw [he]
      omega
    have h2 : k * (p + 1) ≤ k * ((p / 10 ^ (m - w) + 1) * 10 ^ (m - w)) :=
      mmul_l h1 _
    have h3 : k * p + 1 ≤ k * (p + 1) := by
      have e : k * (p + 1) = k * p + k := by rw [Nat.mul_succ]
      omega
    exact h3.trans h2
  have hge : 10 ^ (m - 1) < k * p + 1 := by
    have e : 10 ^ (w - 1) * 10 ^ (m - w) = 10 ^ (m - 1) := by
      rw [← pow_add]; congr 1; omega
    have h1 : 10 ^ (w - 1) * 10 ^ (m - w) ≤ (p / 10 ^ (m - w)) * 10 ^ (m - w) :=
      mmul_r hPlo _
    have hpk : p / 10 ^ (m - w) ≤ k * (p / 10 ^ (m - w)) := by
      have hk1 : (1 : ℕ) ≤ k := by omega
      calc p / 10 ^ (m - w) = 1 * (p / 10 ^ (m - w)) := by ring
        _ ≤ k * (p / 10 ^ (m - w)) := mmul_r hk1 _
    have h2 : (p / 10 ^ (m - w)) * 10 ^ (m - w) ≤
        k * (p / 10 ^ (m - w)) * 10 ^ (m - w) := mmul_r hpk _
    have h3 : 10 ^ (m - 1) ≤ k * (p / 10 ^ (m - w)) * 10 ^ (m - w) := by
      rw [← e]
      exact h1.trans h2
    omega
  have hlt : k * p + 1 < 10 ^ (m + S) := by
    have e1 : 10 ^ w * 10 ^ (m - w) = 10 ^ m := by
      rw [← pow_add]; congr 1; omega
    have h1 : k * p + 1 ≤ k * 10 ^ m := by
      have hPT : (p / 10 ^ (m - w) + 1) * 10 ^ (m - w) ≤ 10 ^ m := by
        have hA : (p / 10 ^ (m - w) + 1) * 10 ^ (m - w) ≤
            10 ^ w * 10 ^ (m - w) :=
          mmul_r (by omega : p / 10 ^ (m - w) + 1 ≤ 10 ^ w) _
        rwa [e1] at hA
      have h2 : k * ((p / 10 ^ (m - w) + 1) * 10 ^ (m - w)) ≤ k * 10 ^ m :=
        mmul_l hPT _
      omega
    have e2 : 10 ^ S * 10 ^ m = 10 ^ (m + S) := by
      rw [← pow_add]; congr 1; omega
    have hk1 : k + 1 ≤ 10 ^ S := by omega
    have hle : (k + 1) * 10 ^ m ≤ 10 ^ S * 10 ^ m := mmul_r hk1 _
    have hd : (k + 1) * 10 ^ m = k * 10 ^ m + 10 ^ m := by ring
    have hT : 0 < 10 ^ m := by positivity
    calc k * p + 1 ≤ k * 10 ^ m := h1
      _ < 10 ^ S * 10 ^ m := by omega
      _ = 10 ^ (m + S) := e2
  have hm'lo : m ≤ m' := by
    by_contra h
    push Not at h
    have h' : m' ≤ m - 1 := by omega
    have e : 10 ^ m' ≤ 10 ^ (m - 1) := pow_le_pow_right₀ (by norm_num) h'
    have : k * p + 1 < 10 ^ (m - 1) := lt_of_lt_of_le hq_hi e
    omega
  have hm'hi : m' ≤ m + S := by
    by_contra h
    push Not at h
    have : 10 ^ (m + S) ≤ 10 ^ (m' - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    omega
  have hm'w : w ≤ m' := by omega
  have hLq1 : (k * p + 1) / 10 ^ (m' - w) * 10 ^ (m' - w) ≤ k * p + 1 := by
    have e := Nat.div_add_mod (k * p + 1) (10 ^ (m' - w))
    rw [mul_comm ((k * p + 1) / 10 ^ (m' - w)) (10 ^ (m' - w))]
    omega
  have hLq2 : k * p + 1 < ((k * p + 1) / 10 ^ (m' - w) + 1) * 10 ^ (m' - w) := by
    have e := Nat.div_add_mod (k * p + 1) (10 ^ (m' - w))
    have hm := Nat.mod_lt (k * p + 1) (by positivity : (0 : ℕ) < 10 ^ (m' - w))
    have h4 : 10 ^ (m' - w) * ((k * p + 1) / 10 ^ (m' - w)) + 10 ^ (m' - w) =
        ((k * p + 1) / 10 ^ (m' - w) + 1) * 10 ^ (m' - w) := by ring
    omega
  have hLlo : 10 ^ (w - 1) ≤ (k * p + 1) / 10 ^ (m' - w) := by
    by_contra h
    push Not at h
    have hP1 : (k * p + 1) / 10 ^ (m' - w) + 1 ≤ 10 ^ (w - 1) := by omega
    have e : 10 ^ (w - 1) * 10 ^ (m' - w) = 10 ^ (m' - 1) := by
      rw [← pow_add]; congr 1; omega
    have : k * p + 1 < 10 ^ (m' - 1) := by
      calc k * p + 1 < ((k * p + 1) / 10 ^ (m' - w) + 1) * 10 ^ (m' - w) := hLq2
        _ ≤ 10 ^ (w - 1) * 10 ^ (m' - w) := mmul_r hP1 _
        _ = 10 ^ (m' - 1) := e
    omega
  have hLhi : (k * p + 1) / 10 ^ (m' - w) < 10 ^ w := by
    by_contra h
    push Not at h
    have h2 : 10 ^ w * 10 ^ (m' - w) ≤
        (k * p + 1) / 10 ^ (m' - w) * 10 ^ (m' - w) := mmul_r h _
    have e : 10 ^ w * 10 ^ (m' - w) = 10 ^ m' := by
      rw [← pow_add]; congr 1; omega
    rw [e] at h2
    have h5 : 10 ^ m' ≤ k * p + 1 := h2.trans hLq1
    omega
  -- renversements palindromiques
  have hprev : p % 10 ^ w = revW w (p / 10 ^ (m - w)) := low_rev hp hwm
  have hqrev : (k * p + 1) % 10 ^ w =
      revW w ((k * p + 1) / 10 ^ (m' - w)) := low_rev hq hm'w
  have hqmod : (k * p + 1) % 10 ^ w =
      (k * revW w (p / 10 ^ (m - w)) + 1) % 10 ^ w := by
    have hN : 1 < 10 ^ w := by
      calc (1 : ℕ) < 10 ^ 1 := by norm_num
        _ ≤ 10 ^ w := pow_le_pow_right₀ (by norm_num) hw
    have step1 : (k * p + 1) % 10 ^ w = (k * (p % 10 ^ w) + 1) % 10 ^ w := by
      have e1 : (k * p) % 10 ^ w = (k * (p % 10 ^ w)) % 10 ^ w := by
        conv_lhs => rw [Nat.mul_mod]
        conv_rhs => rw [Nat.mul_mod, Nat.mod_mod]
      have e2 : (k * p + 1) % 10 ^ w = ((k * p) % 10 ^ w + 1) % 10 ^ w := by
        have e := Nat.add_mod (k * p) 1 (10 ^ w)
        rwa [Nat.mod_eq_of_lt hN] at e
      have e3 : ((k * p) % 10 ^ w + 1) % 10 ^ w =
          (k * (p % 10 ^ w) + 1) % 10 ^ w := by
        rw [e1]
        have e := Nat.add_mod (k * (p % 10 ^ w)) 1 (10 ^ w)
        rw [Nat.mod_eq_of_lt hN] at e
        exact e.symm
      rw [e2, e3]
    rwa [hprev] at step1
  have hLval : (k * p + 1) / 10 ^ (m' - w) =
      revW w (k * revW w (p / 10 ^ (m - w)) + 1) := by
    have h2 : (k * p + 1) / 10 ^ (m' - w) =
        revW w (revW w ((k * p + 1) / 10 ^ (m' - w))) := (revW_invol hLhi).symm
    rw [← hqrev] at h2
    rw [hqmod] at h2
    rw [← revW_mod] at h2
    exact h2
  -- recouvrement d'intervalles au niveau s = m' - m
  have hA : revW w (k * revW w (p / 10 ^ (m - w)) + 1) * 10 ^ (m' - m) ≤
      k * (p / 10 ^ (m - w) + 1) := by
    have h1 : (k * p + 1) / 10 ^ (m' - w) * 10 ^ (m' - w) ≤
        k * ((p / 10 ^ (m - w) + 1) * 10 ^ (m - w)) := hLq1.trans hqhi
    have e : (k * p + 1) / 10 ^ (m' - w) * 10 ^ (m' - w) =
        (k * p + 1) / 10 ^ (m' - w) * (10 ^ (m' - m) * 10 ^ (m - w)) := by
      rw [← pow_add, show m' - m + (m - w) = m' - w by omega]
    have e2 : (k * p + 1) / 10 ^ (m' - w) * (10 ^ (m' - m) * 10 ^ (m - w)) =
        (k * p + 1) / 10 ^ (m' - w) * 10 ^ (m' - m) * 10 ^ (m - w) := by ring
    rw [e, e2] at h1
    rw [hLval] at h1
    by_contra hcon
    push Not at hcon
    have hcon' : k * (p / 10 ^ (m - w) + 1) + 1 ≤
        revW w (k * revW w (p / 10 ^ (m - w)) + 1) * 10 ^ (m' - m) := by omega
    have h3 : (k * (p / 10 ^ (m - w) + 1) + 1) * 10 ^ (m - w) ≤
        revW w (k * revW w (p / 10 ^ (m - w)) + 1) * 10 ^ (m' - m) * 10 ^ (m - w) :=
      mmul_r hcon' _
    have he : (k * (p / 10 ^ (m - w) + 1) + 1) * 10 ^ (m - w) =
        k * ((p / 10 ^ (m - w) + 1) * 10 ^ (m - w)) + 10 ^ (m - w) := by ring
    rw [he] at h3
    have hT : 0 < 10 ^ (m - w) := by positivity
    omega
  have hB : k * (p / 10 ^ (m - w)) <
      (revW w (k * revW w (p / 10 ^ (m - w)) + 1) + 1) * 10 ^ (m' - m) := by
    have h1 : k * (p / 10 ^ (m - w)) * 10 ^ (m - w) <
        ((k * p + 1) / 10 ^ (m' - w) + 1) * 10 ^ (m' - w) := hqlo.trans hLq2
    have e : ((k * p + 1) / 10 ^ (m' - w) + 1) * 10 ^ (m' - w) =
        ((k * p + 1) / 10 ^ (m' - w) + 1) * (10 ^ (m' - m) * 10 ^ (m - w)) := by
      rw [← pow_add, show m' - m + (m - w) = m' - w by omega]
    have e2 : ((k * p + 1) / 10 ^ (m' - w) + 1) * (10 ^ (m' - m) * 10 ^ (m - w)) =
        ((k * p + 1) / 10 ^ (m' - w) + 1) * 10 ^ (m' - m) * 10 ^ (m - w) := by ring
    rw [e, e2] at h1
    rw [hLval] at h1
    by_contra hcon
    push Not at hcon
    have h3 : (revW w (k * revW w (p / 10 ^ (m - w)) + 1) + 1) * 10 ^ (m' - m) *
        10 ^ (m - w) ≤ k * (p / 10 ^ (m - w)) * 10 ^ (m - w) :=
      mmul_r hcon _
    omega
  have hklo : 10 ^ (w - 1) ≤ revW w (k * revW w (p / 10 ^ (m - w)) + 1) :=
    hLval ▸ hLlo
  -- conclusion : okP = false
  unfold okP
  apply decide_false
  intro h
  rcases h with hlt | hall
  · omega
  · have hs : m' - m < S + 1 := by omega
    obtain c | c := hall (m' - m) hs
    · omega
    · omega

/-- `P ∈ cand` et `okP = false` impliquent `P ∈ escapesIn`. -/
theorem mem_escapesIn {k w S P : ℕ} {cand : List ℕ} (hP : P ∈ cand)
    (hok : okP k w S P = false) : P ∈ escapesIn k w S cand := by
  simp [escapesIn, hP, hok]

/-- Combinateur : liste d'échappées vide ⇒ contradiction. -/
theorem zero_of_escapes {k w S : ℕ} (hk : 2 ≤ k) (hkS : k < 10 ^ S) (hw : 1 ≤ w)
    {p m m' : ℕ} (hp : IsPal p m) (hq : IsPal (k * p + 1) m') (hwm : w ≤ m)
    {cand : List ℕ} (hP : p / 10 ^ (m - w) ∈ cand)
    (hc : escapesIn k w S cand = []) : False := by
  have e := prefix_escapes hk hkS hw hp hq hwm
  have hmem := mem_escapesIn hP e
  rw [hc] at hmem
  simp at hmem

-- ===== profondeur 1 : `escapesIn k 1 2 [1..9] = ∅` =====

theorem no_wit_12 {p m m' : ℕ} (hp : IsPal p m) (hq : IsPal (12 * p + 1) m') :
    False := by
  have hm : 1 ≤ m := pal_one_le hp
  have r1 : p / 10 ^ (m - 1) ∈ List.range' 1 9 := by
    have h := prefix_range hp (w := 1) (by norm_num) hm
    exact h
  exact zero_of_escapes (w := 1) (S := 2) (by norm_num) (by norm_num)
    (by norm_num) hp hq hm r1 (by decide)

theorem no_wit_31 {p m m' : ℕ} (hp : IsPal p m) (hq : IsPal (31 * p + 1) m') :
    False := by
  have hm : 1 ≤ m := pal_one_le hp
  have r1 : p / 10 ^ (m - 1) ∈ List.range' 1 9 := by
    have h := prefix_range hp (w := 1) (by norm_num) hm
    exact h
  exact zero_of_escapes (w := 1) (S := 2) (by norm_num) (by norm_num)
    (by norm_num) hp hq hm r1 (by decide)

theorem no_wit_37 {p m m' : ℕ} (hp : IsPal p m) (hq : IsPal (37 * p + 1) m') :
    False := by
  have hm : 1 ≤ m := pal_one_le hp
  have r1 : p / 10 ^ (m - 1) ∈ List.range' 1 9 := by
    have h := prefix_range hp (w := 1) (by norm_num) hm
    exact h
  exact zero_of_escapes (w := 1) (S := 2) (by norm_num) (by norm_num)
    (by norm_num) hp hq hm r1 (by decide)

theorem no_wit_41 {p m m' : ℕ} (hp : IsPal p m) (hq : IsPal (41 * p + 1) m') :
    False := by
  have hm : 1 ≤ m := pal_one_le hp
  have r1 : p / 10 ^ (m - 1) ∈ List.range' 1 9 := by
    have h := prefix_range hp (w := 1) (by norm_num) hm
    exact h
  exact zero_of_escapes (w := 1) (S := 2) (by norm_num) (by norm_num)
    (by norm_num) hp hq hm r1 (by decide)

theorem no_wit_42 {p m m' : ℕ} (hp : IsPal p m) (hq : IsPal (42 * p + 1) m') :
    False := by
  have hm : 1 ≤ m := pal_one_le hp
  have r1 : p / 10 ^ (m - 1) ∈ List.range' 1 9 := by
    have h := prefix_range hp (w := 1) (by norm_num) hm
    exact h
  exact zero_of_escapes (w := 1) (S := 2) (by norm_num) (by norm_num)
    (by norm_num) hp hq hm r1 (by decide)

theorem no_wit_51 {p m m' : ℕ} (hp : IsPal p m) (hq : IsPal (51 * p + 1) m') :
    False := by
  have hm : 1 ≤ m := pal_one_le hp
  have r1 : p / 10 ^ (m - 1) ∈ List.range' 1 9 := by
    have h := prefix_range hp (w := 1) (by norm_num) hm
    exact h
  exact zero_of_escapes (w := 1) (S := 2) (by norm_num) (by norm_num)
    (by norm_num) hp hq hm r1 (by decide)

theorem no_wit_53 {p m m' : ℕ} (hp : IsPal p m) (hq : IsPal (53 * p + 1) m') :
    False := by
  have hm : 1 ≤ m := pal_one_le hp
  have r1 : p / 10 ^ (m - 1) ∈ List.range' 1 9 := by
    have h := prefix_range hp (w := 1) (by norm_num) hm
    exact h
  exact zero_of_escapes (w := 1) (S := 2) (by norm_num) (by norm_num)
    (by norm_num) hp hq hm r1 (by decide)

theorem no_wit_61 {p m m' : ℕ} (hp : IsPal p m) (hq : IsPal (61 * p + 1) m') :
    False := by
  have hm : 1 ≤ m := pal_one_le hp
  have r1 : p / 10 ^ (m - 1) ∈ List.range' 1 9 := by
    have h := prefix_range hp (w := 1) (by norm_num) hm
    exact h
  exact zero_of_escapes (w := 1) (S := 2) (by norm_num) (by norm_num)
    (by norm_num) hp hq hm r1 (by decide)

theorem no_wit_64 {p m m' : ℕ} (hp : IsPal p m) (hq : IsPal (64 * p + 1) m') :
    False := by
  have hm : 1 ≤ m := pal_one_le hp
  have r1 : p / 10 ^ (m - 1) ∈ List.range' 1 9 := by
    have h := prefix_range hp (w := 1) (by norm_num) hm
    exact h
  exact zero_of_escapes (w := 1) (S := 2) (by norm_num) (by norm_num)
    (by norm_num) hp hq hm r1 (by decide)

theorem no_wit_71 {p m m' : ℕ} (hp : IsPal p m) (hq : IsPal (71 * p + 1) m') :
    False := by
  have hm : 1 ≤ m := pal_one_le hp
  have r1 : p / 10 ^ (m - 1) ∈ List.range' 1 9 := by
    have h := prefix_range hp (w := 1) (by norm_num) hm
    exact h
  exact zero_of_escapes (w := 1) (S := 2) (by norm_num) (by norm_num)
    (by norm_num) hp hq hm r1 (by decide)

theorem no_wit_81 {p m m' : ℕ} (hp : IsPal p m) (hq : IsPal (81 * p + 1) m') :
    False := by
  have hm : 1 ≤ m := pal_one_le hp
  have r1 : p / 10 ^ (m - 1) ∈ List.range' 1 9 := by
    have h := prefix_range hp (w := 1) (by norm_num) hm
    exact h
  exact zero_of_escapes (w := 1) (S := 2) (by norm_num) (by norm_num)
    (by norm_num) hp hq hm r1 (by decide)

theorem no_wit_86 {p m m' : ℕ} (hp : IsPal p m) (hq : IsPal (86 * p + 1) m') :
    False := by
  have hm : 1 ≤ m := pal_one_le hp
  have r1 : p / 10 ^ (m - 1) ∈ List.range' 1 9 := by
    have h := prefix_range hp (w := 1) (by norm_num) hm
    exact h
  exact zero_of_escapes (w := 1) (S := 2) (by norm_num) (by norm_num)
    (by norm_num) hp hq hm r1 (by decide)

theorem no_wit_91 {p m m' : ℕ} (hp : IsPal p m) (hq : IsPal (91 * p + 1) m') :
    False := by
  have hm : 1 ≤ m := pal_one_le hp
  have r1 : p / 10 ^ (m - 1) ∈ List.range' 1 9 := by
    have h := prefix_range hp (w := 1) (by norm_num) hm
    exact h
  exact zero_of_escapes (w := 1) (S := 2) (by norm_num) (by norm_num)
    (by norm_num) hp hq hm r1 (by decide)

theorem no_wit_96 {p m m' : ℕ} (hp : IsPal p m) (hq : IsPal (96 * p + 1) m') :
    False := by
  have hm : 1 ≤ m := pal_one_le hp
  have r1 : p / 10 ^ (m - 1) ∈ List.range' 1 9 := by
    have h := prefix_range hp (w := 1) (by norm_num) hm
    exact h
  exact zero_of_escapes (w := 1) (S := 2) (by norm_num) (by norm_num)
    (by norm_num) hp hq hm r1 (by decide)

-- ===== profondeur 2 =====

theorem no_wit_17 {p m m' : ℕ} (hp : IsPal p m) (hq : IsPal (17 * p + 1) m') :
    False := by
  have hm : 1 ≤ m := pal_one_le hp
  have e1 := prefix_escapes (k := 17) (w := 1) (S := 2) (by norm_num)
    (by norm_num) (by norm_num) hp hq hm
  have r1 : p / 10 ^ (m - 1) ∈ List.range' 1 9 := by
    have h := prefix_range hp (w := 1) (by norm_num) hm
    exact h
  have hE1 : escapesIn 17 1 2 (List.range' 1 9) = [2] := by decide
  have hP1 : p / 10 ^ (m - 1) = 2 := by
    have hmem := mem_escapesIn r1 e1
    rw [hE1] at hmem
    simpa using hmem
  rcases Nat.lt_or_ge m 2 with hm12 | hm12
  · have hm1 : m = 1 := by omega
    subst hm1
    have hpv : p = 2 := by simpa using hP1
    subst hpv
    exact not_pal_of (a := 2) hq (by norm_num) (by norm_num) (by decide)
  · have r2 : p / 10 ^ (m - 2) ∈ List.range' 10 90 := by
      have h := prefix_range hp (w := 2) (by norm_num) hm12
      exact h
    exact zero_of_escapes (w := 2) (S := 2) (by norm_num) (by norm_num)
      (by norm_num) hp hq hm12 r2 (by decide)

theorem no_wit_23 {p m m' : ℕ} (hp : IsPal p m) (hq : IsPal (23 * p + 1) m') :
    False := by
  have hm : 1 ≤ m := pal_one_le hp
  have e1 := prefix_escapes (k := 23) (w := 1) (S := 2) (by norm_num)
    (by norm_num) (by norm_num) hp hq hm
  have r1 : p / 10 ^ (m - 1) ∈ List.range' 1 9 := by
    have h := prefix_range hp (w := 1) (by norm_num) hm
    exact h
  have hE1 : escapesIn 23 1 2 (List.range' 1 9) = [1] := by decide
  have hP1 : p / 10 ^ (m - 1) = 1 := by
    have hmem := mem_escapesIn r1 e1
    rw [hE1] at hmem
    simpa using hmem
  rcases Nat.lt_or_ge m 2 with hm12 | hm12
  · have hm1 : m = 1 := by omega
    subst hm1
    have hpv : p = 1 := by simpa using hP1
    subst hpv
    exact not_pal_of (a := 2) hq (by norm_num) (by norm_num) (by decide)
  · have r2 : p / 10 ^ (m - 2) ∈ List.range' 10 90 := by
      have h := prefix_range hp (w := 2) (by norm_num) hm12
      exact h
    exact zero_of_escapes (w := 2) (S := 2) (by norm_num) (by norm_num)
      (by norm_num) hp hq hm12 r2 (by decide)

theorem no_wit_74 {p m m' : ℕ} (hp : IsPal p m) (hq : IsPal (74 * p + 1) m') :
    False := by
  have hm : 1 ≤ m := pal_one_le hp
  have e1 := prefix_escapes (k := 74) (w := 1) (S := 2) (by norm_num)
    (by norm_num) (by norm_num) hp hq hm
  have r1 : p / 10 ^ (m - 1) ∈ List.range' 1 9 := by
    have h := prefix_range hp (w := 1) (by norm_num) hm
    exact h
  have hE1 : escapesIn 74 1 2 (List.range' 1 9) = [6, 9] := by decide
  have hP1 : p / 10 ^ (m - 1) ∈ ([6, 9] : List ℕ) := by
    have hmem := mem_escapesIn r1 e1
    rwa [hE1] at hmem
  rcases Nat.lt_or_ge m 2 with hm12 | hm12
  · have hm1 : m = 1 := by omega
    subst hm1
    have hpv : p = 6 ∨ p = 9 := by simpa using hP1
    rcases hpv with rfl | rfl <;>
      exact not_pal_of (a := 3) hq (by norm_num) (by norm_num) (by decide)
  · have r2 : p / 10 ^ (m - 2) ∈ List.range' 10 90 := by
      have h := prefix_range hp (w := 2) (by norm_num) hm12
      exact h
    exact zero_of_escapes (w := 2) (S := 2) (by norm_num) (by norm_num)
      (by norm_num) hp hq hm12 r2 (by decide)

theorem no_wit_101 {p m m' : ℕ} (hp : IsPal p m) (hq : IsPal (101 * p + 1) m') :
    False := by
  have hm : 1 ≤ m := pal_one_le hp
  have e1 := prefix_escapes (k := 101) (w := 1) (S := 3) (by norm_num)
    (by norm_num) (by norm_num) hp hq hm
  have r1 : p / 10 ^ (m - 1) ∈ List.range' 1 9 := by
    have h := prefix_range hp (w := 1) (by norm_num) hm
    exact h
  have hE1 : escapesIn 101 1 3 (List.range' 1 9) = [1, 2, 3, 4, 5, 6, 7, 8] := by
    decide
  have hP1 : p / 10 ^ (m - 1) ∈ ([1, 2, 3, 4, 5, 6, 7, 8] : List ℕ) := by
    have hmem := mem_escapesIn r1 e1
    rwa [hE1] at hmem
  rcases Nat.lt_or_ge m 2 with hm12 | hm12
  · have hm1 : m = 1 := by omega
    subst hm1
    have hpv : p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 ∨ p = 8 := by
      simpa using hP1
    rcases hpv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact not_pal_of (a := 3) hq (by norm_num) (by norm_num) (by decide)
  · have r2 : p / 10 ^ (m - 2) ∈ List.range' 10 90 := by
      have h := prefix_range hp (w := 2) (by norm_num) hm12
      exact h
    exact zero_of_escapes (w := 2) (S := 3) (by norm_num) (by norm_num)
      (by norm_num) hp hq hm12 r2 (by decide)

theorem no_wit_103 {p m m' : ℕ} (hp : IsPal p m) (hq : IsPal (103 * p + 1) m') :
    False := by
  have hm : 1 ≤ m := pal_one_le hp
  have e1 := prefix_escapes (k := 103) (w := 1) (S := 3) (by norm_num)
    (by norm_num) (by norm_num) hp hq hm
  have r1 : p / 10 ^ (m - 1) ∈ List.range' 1 9 := by
    have h := prefix_range hp (w := 1) (by norm_num) hm
    exact h
  have hE1 : escapesIn 103 1 3 (List.range' 1 9) = [5] := by decide
  have hP1 : p / 10 ^ (m - 1) = 5 := by
    have hmem := mem_escapesIn r1 e1
    rw [hE1] at hmem
    simpa using hmem
  rcases Nat.lt_or_ge m 2 with hm12 | hm12
  · have hm1 : m = 1 := by omega
    subst hm1
    have hpv : p = 5 := by simpa using hP1
    subst hpv
    exact not_pal_of (a := 3) hq (by norm_num) (by norm_num) (by decide)
  · have r2 : p / 10 ^ (m - 2) ∈ List.range' 10 90 := by
      have h := prefix_range hp (w := 2) (by norm_num) hm12
      exact h
    exact zero_of_escapes (w := 2) (S := 3) (by norm_num) (by norm_num)
      (by norm_num) hp hq hm12 r2 (by decide)

-- ===== profondeur 3 =====

theorem no_wit_48 {p m m' : ℕ} (hp : IsPal p m) (hq : IsPal (48 * p + 1) m') :
    False := by
  have hm : 1 ≤ m := pal_one_le hp
  have e1 := prefix_escapes (k := 48) (w := 1) (S := 2) (by norm_num)
    (by norm_num) (by norm_num) hp hq hm
  have r1 : p / 10 ^ (m - 1) ∈ List.range' 1 9 := by
    have h := prefix_range hp (w := 1) (by norm_num) hm
    exact h
  have hE1 : escapesIn 48 1 2 (List.range' 1 9) = [1] := by decide
  have hP1 : p / 10 ^ (m - 1) = 1 := by
    have hmem := mem_escapesIn r1 e1
    rw [hE1] at hmem
    simpa using hmem
  rcases Nat.lt_or_ge m 2 with hm12 | hm12
  · have hm1 : m = 1 := by omega
    subst hm1
    have hpv : p = 1 := by simpa using hP1
    subst hpv
    exact not_pal_of (a := 2) hq (by norm_num) (by norm_num) (by decide)
  · have e2 := prefix_escapes (k := 48) (w := 2) (S := 2) (by norm_num)
      (by norm_num) (by norm_num) hp hq hm12
    have r2 : p / 10 ^ (m - 2) ∈ List.range' 10 90 := by
      have h := prefix_range hp (w := 2) (by norm_num) hm12
      exact h
    have hE2 : escapesIn 48 2 2 (List.range' 10 90) = [19] := by decide
    have hP2 : p / 10 ^ (m - 2) = 19 := by
      have hmem := mem_escapesIn r2 e2
      rw [hE2] at hmem
      simpa using hmem
    rcases Nat.lt_or_ge m 3 with hm23 | hm23
    · have hm2 : m = 2 := by omega
      subst hm2
      have hpv : p = 19 := by simpa using hP2
      subst hpv
      have hs := hp.sym 0 (by norm_num)
      have hd : dgt 19 0 ≠ dgt 19 1 := by decide
      exact hd hs
    · have r3 : p / 10 ^ (m - 3) ∈ List.range' 190 10 := by
        have hx := prefix_ext (p := p) (m := m) (w := 2) (by omega)
        rw [hP2] at hx
        have hd : dgt p (m - 1 - 2) < 10 := dgt_lt _ _
        rw [List.mem_range']
        refine ⟨dgt p (m - 1 - 2), hd, ?_⟩
        have hidx : m - (2 + 1) = m - 3 := by omega
        rw [hidx] at hx
        omega
      exact zero_of_escapes (w := 3) (S := 2) (by norm_num) (by norm_num)
        (by norm_num) hp hq hm23 r3 (by decide)

theorem no_wit_79 {p m m' : ℕ} (hp : IsPal p m) (hq : IsPal (79 * p + 1) m') :
    False := by
  have hm : 1 ≤ m := pal_one_le hp
  have e1 := prefix_escapes (k := 79) (w := 1) (S := 2) (by norm_num)
    (by norm_num) (by norm_num) hp hq hm
  have r1 : p / 10 ^ (m - 1) ∈ List.range' 1 9 := by
    have h := prefix_range hp (w := 1) (by norm_num) hm
    exact h
  have hE1 : escapesIn 79 1 2 (List.range' 1 9) = [6] := by decide
  have hP1 : p / 10 ^ (m - 1) = 6 := by
    have hmem := mem_escapesIn r1 e1
    rw [hE1] at hmem
    simpa using hmem
  rcases Nat.lt_or_ge m 2 with hm12 | hm12
  · have hm1 : m = 1 := by omega
    subst hm1
    have hpv : p = 6 := by simpa using hP1
    subst hpv
    exact not_pal_of (a := 3) hq (by norm_num) (by norm_num) (by decide)
  · have e2 := prefix_escapes (k := 79) (w := 2) (S := 2) (by norm_num)
      (by norm_num) (by norm_num) hp hq hm12
    have r2 : p / 10 ^ (m - 2) ∈ List.range' 10 90 := by
      have h := prefix_range hp (w := 2) (by norm_num) hm12
      exact h
    have hE2 : escapesIn 79 2 2 (List.range' 10 90) = [65] := by decide
    have hP2 : p / 10 ^ (m - 2) = 65 := by
      have hmem := mem_escapesIn r2 e2
      rw [hE2] at hmem
      simpa using hmem
    rcases Nat.lt_or_ge m 3 with hm23 | hm23
    · have hm2 : m = 2 := by omega
      subst hm2
      have hpv : p = 65 := by simpa using hP2
      subst hpv
      have hs := hp.sym 0 (by norm_num)
      have hd : dgt 65 0 ≠ dgt 65 1 := by decide
      exact hd hs
    · have r3 : p / 10 ^ (m - 3) ∈ List.range' 650 10 := by
        have hx := prefix_ext (p := p) (m := m) (w := 2) (by omega)
        rw [hP2] at hx
        have hd : dgt p (m - 1 - 2) < 10 := dgt_lt _ _
        rw [List.mem_range']
        refine ⟨dgt p (m - 1 - 2), hd, ?_⟩
        have hidx : m - (2 + 1) = m - 3 := by omega
        rw [hidx] at hx
        omega
      exact zero_of_escapes (w := 3) (S := 2) (by norm_num) (by norm_num)
        (by norm_num) hp hq hm23 r3 (by decide)

-- ===== capstones : `a(k) = 0` pour les 21 zéros affichés =====

/-- A083837(12) = 0 : inexistence universelle. -/
theorem A083837_12_zero : ¬ ∃ p m m', IsPal p m ∧ IsPal (12 * p + 1) m' := by
  rintro ⟨p, m, m', hp, hq⟩
  exact no_wit_12 hp hq

/-- A083837(17) = 0 : inexistence universelle. -/
theorem A083837_17_zero : ¬ ∃ p m m', IsPal p m ∧ IsPal (17 * p + 1) m' := by
  rintro ⟨p, m, m', hp, hq⟩
  exact no_wit_17 hp hq

/-- A083837(23) = 0 : inexistence universelle. -/
theorem A083837_23_zero : ¬ ∃ p m m', IsPal p m ∧ IsPal (23 * p + 1) m' := by
  rintro ⟨p, m, m', hp, hq⟩
  exact no_wit_23 hp hq

/-- A083837(31) = 0 : inexistence universelle. -/
theorem A083837_31_zero : ¬ ∃ p m m', IsPal p m ∧ IsPal (31 * p + 1) m' := by
  rintro ⟨p, m, m', hp, hq⟩
  exact no_wit_31 hp hq

/-- A083837(37) = 0 : inexistence universelle. -/
theorem A083837_37_zero : ¬ ∃ p m m', IsPal p m ∧ IsPal (37 * p + 1) m' := by
  rintro ⟨p, m, m', hp, hq⟩
  exact no_wit_37 hp hq

/-- A083837(41) = 0 : inexistence universelle. -/
theorem A083837_41_zero : ¬ ∃ p m m', IsPal p m ∧ IsPal (41 * p + 1) m' := by
  rintro ⟨p, m, m', hp, hq⟩
  exact no_wit_41 hp hq

/-- A083837(42) = 0 : inexistence universelle. -/
theorem A083837_42_zero : ¬ ∃ p m m', IsPal p m ∧ IsPal (42 * p + 1) m' := by
  rintro ⟨p, m, m', hp, hq⟩
  exact no_wit_42 hp hq

/-- A083837(48) = 0 : inexistence universelle. -/
theorem A083837_48_zero : ¬ ∃ p m m', IsPal p m ∧ IsPal (48 * p + 1) m' := by
  rintro ⟨p, m, m', hp, hq⟩
  exact no_wit_48 hp hq

/-- A083837(51) = 0 : inexistence universelle. -/
theorem A083837_51_zero : ¬ ∃ p m m', IsPal p m ∧ IsPal (51 * p + 1) m' := by
  rintro ⟨p, m, m', hp, hq⟩
  exact no_wit_51 hp hq

/-- A083837(53) = 0 : inexistence universelle. -/
theorem A083837_53_zero : ¬ ∃ p m m', IsPal p m ∧ IsPal (53 * p + 1) m' := by
  rintro ⟨p, m, m', hp, hq⟩
  exact no_wit_53 hp hq

/-- A083837(61) = 0 : inexistence universelle. -/
theorem A083837_61_zero : ¬ ∃ p m m', IsPal p m ∧ IsPal (61 * p + 1) m' := by
  rintro ⟨p, m, m', hp, hq⟩
  exact no_wit_61 hp hq

/-- A083837(64) = 0 : inexistence universelle. -/
theorem A083837_64_zero : ¬ ∃ p m m', IsPal p m ∧ IsPal (64 * p + 1) m' := by
  rintro ⟨p, m, m', hp, hq⟩
  exact no_wit_64 hp hq

/-- A083837(71) = 0 : inexistence universelle. -/
theorem A083837_71_zero : ¬ ∃ p m m', IsPal p m ∧ IsPal (71 * p + 1) m' := by
  rintro ⟨p, m, m', hp, hq⟩
  exact no_wit_71 hp hq

/-- A083837(74) = 0 : inexistence universelle. -/
theorem A083837_74_zero : ¬ ∃ p m m', IsPal p m ∧ IsPal (74 * p + 1) m' := by
  rintro ⟨p, m, m', hp, hq⟩
  exact no_wit_74 hp hq

/-- A083837(79) = 0 : inexistence universelle. -/
theorem A083837_79_zero : ¬ ∃ p m m', IsPal p m ∧ IsPal (79 * p + 1) m' := by
  rintro ⟨p, m, m', hp, hq⟩
  exact no_wit_79 hp hq

/-- A083837(81) = 0 : inexistence universelle. -/
theorem A083837_81_zero : ¬ ∃ p m m', IsPal p m ∧ IsPal (81 * p + 1) m' := by
  rintro ⟨p, m, m', hp, hq⟩
  exact no_wit_81 hp hq

/-- A083837(86) = 0 : inexistence universelle. -/
theorem A083837_86_zero : ¬ ∃ p m m', IsPal p m ∧ IsPal (86 * p + 1) m' := by
  rintro ⟨p, m, m', hp, hq⟩
  exact no_wit_86 hp hq

/-- A083837(91) = 0 : inexistence universelle. -/
theorem A083837_91_zero : ¬ ∃ p m m', IsPal p m ∧ IsPal (91 * p + 1) m' := by
  rintro ⟨p, m, m', hp, hq⟩
  exact no_wit_91 hp hq

/-- A083837(96) = 0 : inexistence universelle. -/
theorem A083837_96_zero : ¬ ∃ p m m', IsPal p m ∧ IsPal (96 * p + 1) m' := by
  rintro ⟨p, m, m', hp, hq⟩
  exact no_wit_96 hp hq

/-- A083837(101) = 0 : inexistence universelle. -/
theorem A083837_101_zero : ¬ ∃ p m m', IsPal p m ∧ IsPal (101 * p + 1) m' := by
  rintro ⟨p, m, m', hp, hq⟩
  exact no_wit_101 hp hq

/-- A083837(103) = 0 : inexistence universelle. -/
theorem A083837_103_zero : ¬ ∃ p m m', IsPal p m ∧ IsPal (103 * p + 1) m' := by
  rintro ⟨p, m, m', hp, hq⟩
  exact no_wit_103 hp hq

end A083837
