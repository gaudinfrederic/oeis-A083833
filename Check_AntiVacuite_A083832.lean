import A083832

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Check_AntiVacuite_A083832 : protocole N3 pour A083832

Le theoreme livre est `A083832_alphabet` (module `A083832`,
re-export de `A083832_digits` prouve dans `A083831`) : pour `p`
palindrome a `m` chiffres et `q = 4p+1` palindrome a `m'` chiffres
(`1 ≤ m`), tout chiffre de `q` vaut `1`, `2`, `3`, `5`, `6` ou `9`.

Trois exigences, toutes kernel-pures (`decide`/`rfl`/`norm_num`/
`omega`) :

1. satisfiabilite de la conjonction `IsPal p m ∧ IsPal (4p+1) m'
   ∧ 1 ≤ m` par des membres reels : `p = 8` donne `q = 33`
   (bord `m = 1`, branche `m' = m+1`), `p = 88` donne `q = 353`
   (branche `m' = m+1`, `m` pair) et `p = 131` donne `q = 525`
   (branche `m' = m`, `m` impair) ; `8`, `88`, `131` sont termes
   affiches d'A083831 et `33`, `353`, `525` termes affiches
   d'A083832 ; `sat_via_theorem` instancie le theoreme livre
   lui-meme sur `p = 88` ;
2. ancrage `rfl`/`decide` des conventions (`dgt` little-endian,
   `crry p 0 = 1` pliant le `+1`, `crry 88 1 = 3` en branche
   successeur, `crry 131 1 = 0` en branche meme-longueur) et des
   chiffres de `q` sur les termes documentes `33`, `353`, `525`,
   `52125` ;
3. ablation : chaque hypothese et chaque disjonct est
   indispensable -
   - `hp` : `q = 505 = 4·126+1` est palindrome (`IsPal 505 3`) mais
     `p = 126` ne l'est pas (`dgt 0 = 6 ≠ 1 = dgt 2`) ; sans `hp`
     la conjonction restante est habitee en `(126, 3, 3)` et le
     chiffre `0` de `q` refute la conclusion ;
   - `hq` : `p = 22` est palindrome (`IsPal 22 2`) mais
     `4·22+1 = 89` ne l'est pas (chiffres de bord `9 ≠ 8`) et son
     chiffre `8` est hors alphabet ;
   - `1 ≤ m` : a `m = 0`, `IsPal p 0` est contradictoire
     (`lo : 1 ≤ p` contre `hi : p < 1`) - la garde borne le
     domaine OEIS et `m = 1` est habitee (`sat_m_one`) ;
   - alphabet serre : les six chiffres `{1,2,3,5,6,9}` sont tous
     atteints par des membres verifiant la conjonction complete
     (`1` donne `5`, `2` donne `9`, `8` donne `33`, `131` donne
     `525`, `141` donne `565`, `13031` donne `52125`) - retirer un
     disjonct refute l'enonce sur le membre correspondant.
   Les hypotheses seules ne prouvent pas `False` : le point 1 est
   le certificat machine de consistance ; la variante tactique
   (sous `intro hp hq hm`, `first | omega | simp_all | aesop`
   n'aboutit pas) est verifiee a la revue, jamais automatisee.
-/

open A083831

namespace CheckAntiVacA083832

-- N3.1 - Satisfiabilite de la conjonction des hypotheses.

/-- Conjonction exacte des hypotheses du theoreme, en
`p = 88, m = 2, m' = 3` (`88` terme d'A083831, `353` terme
d'A083832, donnees affichees). -/
theorem sat_conjunction :
    ∃ p m m', IsPal p m ∧ IsPal (4 * p + 1) m' ∧ 1 ≤ m :=
  ⟨88, 2, 3, ⟨by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide⟩, by norm_num⟩

/-- Branche `m' = m+1` : `p = 88`, `q = 353` (membres OEIS
affiches, `m = 2` pair - repdigit `88...8` de la conjecture
d'Israel). -/
theorem sat_succ_branch :
    ∃ p m m', IsPal p m ∧ IsPal (4 * p + 1) m' ∧ 1 ≤ m ∧
      m' = m + 1 :=
  ⟨88, 2, 3, ⟨by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide⟩, by norm_num, by decide⟩

/-- Branche `m' = m` : `p = 131`, `q = 525` (membres OEIS
affiches, `m = 3` impair). -/
theorem sat_same_branch :
    ∃ p m m', IsPal p m ∧ IsPal (4 * p + 1) m' ∧ 1 ≤ m ∧ m' = m :=
  ⟨131, 3, 3, ⟨by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide⟩, by norm_num, by decide⟩

/-- Bord de la garde : `m = 1` est habitee par `p = 8`, `q = 33`
(membres OEIS affiches ; branche `m' = m+1`). -/
theorem sat_m_one :
    ∃ p m m', IsPal p m ∧ IsPal (4 * p + 1) m' ∧ 1 ≤ m ∧ m = 1 :=
  ⟨8, 1, 2, ⟨by decide, by decide, by decide⟩,
    ⟨by decide, by decide, by decide⟩, by norm_num, by decide⟩

/-- Certificat via le theoreme livre : `A083832_alphabet`
s'instancie sur le membre reel `p = 88` (`q = 353`) ; le `5` en
position `1` est couvert par le quatrieme disjonct. -/
theorem sat_via_theorem :
    dgt (4 * 88 + 1) 1 = 1 ∨ dgt (4 * 88 + 1) 1 = 2 ∨
      dgt (4 * 88 + 1) 1 = 3 ∨ dgt (4 * 88 + 1) 1 = 5 ∨
      dgt (4 * 88 + 1) 1 = 6 ∨ dgt (4 * 88 + 1) 1 = 9 :=
  A083832_alphabet (p := 88) (m := 2) (m' := 3)
    (⟨by decide, by decide, by decide⟩ : IsPal 88 2)
    (⟨by decide, by decide, by decide⟩ : IsPal (4 * 88 + 1) 3)
    (by norm_num) 1 (by decide)

-- N3.2 - Ancrage `rfl`/`decide` (conventions du module).

example : dgt 88 0 = 8 := rfl
example : dgt 88 1 = 8 := rfl
example : dgt 131 0 = 1 := by decide
example : dgt 131 1 = 3 := by decide
example : dgt 131 2 = 1 := by decide
example : crry 88 0 = 1 := crry_zero 88
example : crry 88 1 = 3 := by decide
example : crry 131 1 = 0 := by decide
example : dgt (4 * 8 + 1) 0 = 3 := by decide
example : dgt (4 * 8 + 1) 1 = 3 := by decide
example : dgt (4 * 88 + 1) 0 = 3 := by decide
example : dgt (4 * 88 + 1) 1 = 5 := by decide
example : dgt (4 * 88 + 1) 2 = 3 := by decide
example : dgt (4 * 131 + 1) 1 = 2 := by decide
example : dgt (4 * 13031 + 1) 2 = 1 := by decide

-- N3.3 - Ablation : chaque clause est indispensable ; les
-- hypotheses seules ne prouvent pas False (point 1 = certificat).

/-- `hp` indispensable : `q = 505` est palindrome de longueur `3`
et `1 ≤ 3`, mais `p = 126` ne l'est pas (`dgt 0 = 6 ≠ 1 = dgt 2`)
; sans `hp`, le chiffre `0` de `q` refute la conclusion. -/
theorem ablation_needs_ppal :
    IsPal (4 * 126 + 1) 3 ∧ 1 ≤ 3 ∧ dgt (4 * 126 + 1) 1 = 0 ∧
      dgt 126 0 ≠ dgt 126 2 :=
  ⟨⟨by decide, by decide, by decide⟩, by norm_num, by decide,
    by decide⟩

/-- `hq` indispensable : `p = 22` est palindrome (`IsPal 22 2`)
mais `4·22+1 = 89` ne l'est pas (chiffres de bord `9 ≠ 8`) et son
chiffre `8` est hors alphabet `{1,2,3,5,6,9}`. -/
theorem ablation_needs_qpal :
    IsPal 22 2 ∧ dgt (4 * 22 + 1) 1 = 8 ∧
      dgt (4 * 22 + 1) 0 ≠ dgt (4 * 22 + 1) 1 :=
  ⟨⟨by decide, by decide, by decide⟩, by decide, by decide⟩

/-- Garde `1 ≤ m` : a `m = 0`, `IsPal p 0` est contradictoire
(`lo : 1 ≤ p` contre `hi : p < 1`, car `10^(0-1) = 10^0 = 1` en
arithmetique tronquee) - la garde borne le domaine OEIS sans
exclure aucun temoin ; `m = 1` reste habitee (`sat_m_one`). -/
theorem ablation_m_guard : ∀ p : ℕ, ¬ IsPal p 0 := by
  intro p hp
  have hhi : p < 1 := hp.hi
  have hlo : 1 ≤ p := hp.lo
  omega

/-- Alphabet serre : chacun des six chiffres de la conclusion est
atteint par un membre verifiant la conjonction complete -
`5` (`p = 1`, `q = 5`), `9` (`p = 2`, `q = 9`), `3` (`p = 8`,
`q = 33`), `2` (`p = 131`, `q = 525`), `6` (`p = 141`, `q = 565`),
`1` (`p = 13031`, `q = 52125`) ; tous termes des donnees
affichees. Retirer un disjonct refute l'enonce sur le membre
correspondant. -/
theorem ablation_alpha_tight :
    (IsPal 1 1 ∧ IsPal (4 * 1 + 1) 1 ∧ 1 ≤ 1 ∧
      dgt (4 * 1 + 1) 0 = 5) ∧
    (IsPal 2 1 ∧ IsPal (4 * 2 + 1) 1 ∧ 1 ≤ 1 ∧
      dgt (4 * 2 + 1) 0 = 9) ∧
    (IsPal 8 1 ∧ IsPal (4 * 8 + 1) 2 ∧ 1 ≤ 1 ∧
      dgt (4 * 8 + 1) 0 = 3) ∧
    (IsPal 131 3 ∧ IsPal (4 * 131 + 1) 3 ∧ 1 ≤ 3 ∧
      dgt (4 * 131 + 1) 1 = 2) ∧
    (IsPal 141 3 ∧ IsPal (4 * 141 + 1) 3 ∧ 1 ≤ 3 ∧
      dgt (4 * 141 + 1) 1 = 6) ∧
    (IsPal 13031 5 ∧ IsPal (4 * 13031 + 1) 5 ∧ 1 ≤ 5 ∧
      dgt (4 * 13031 + 1) 2 = 1) :=
  ⟨⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩,
      by norm_num, by decide⟩,
    ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩,
      by norm_num, by decide⟩,
    ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩,
      by norm_num, by decide⟩,
    ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩,
      by norm_num, by decide⟩,
    ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩,
      by norm_num, by decide⟩,
    ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩,
      by norm_num, by decide⟩⟩

end CheckAntiVacA083832

#print axioms CheckAntiVacA083832.sat_conjunction
#print axioms CheckAntiVacA083832.sat_succ_branch
#print axioms CheckAntiVacA083832.sat_same_branch
#print axioms CheckAntiVacA083832.sat_m_one
#print axioms CheckAntiVacA083832.sat_via_theorem
#print axioms CheckAntiVacA083832.ablation_needs_ppal
#print axioms CheckAntiVacA083832.ablation_needs_qpal
#print axioms CheckAntiVacA083832.ablation_m_guard
#print axioms CheckAntiVacA083832.ablation_alpha_tight
