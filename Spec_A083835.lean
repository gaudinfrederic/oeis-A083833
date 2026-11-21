import A083835

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Spec_A083835 : énoncé pur auditable (protocole N0, Option B)

La fiche OEIS A083835 (« palindromes `n` tels que `6n+1` est aussi
palindrome », Murthy-Srikanth 2003) ne porte aucune conjecture
commentée ; l'énoncé record est donc la CLASSIFICATION COMPLETE
dans les deux sens, prouvée dans `A083835.lean` (capstone `A083835`) :

  `6p+1` palindrome de longueur `m'`  ⟺
    (`m' = m+1` et `p = 99...9`, débordement `q = 5 9^{m-1} 5`)
    ou
    (`m' = m`, `m` impair et classes alternées `a_j ∈ {0,1}` pour
    `j` pair, `a_j ∈ {2,3}` pour `j` impair - mêmes classes que
    pour `k = 5` / A083833).

Surface minimale : `IsPal`/`dgt` sont réutilisés du module
`A083835` (namespace `A083835`, ouvert ci-dessous) ; zéro
redéfinition, zéro `sorry`, zéro tactique, zéro notation locale.
La fermeture `theorem proven_A083835 : SpecA083835 := ...` vit dans
`Check_Spec_A083835.lean`. L'énoncé recopie la signature exacte du
théorème `A083835` du module homonyme. Les compagnons
`A083836_*` (suite image) relèvent du package A083836, hors
périmètre de cette spec.
-/

open A083835

/-- Énoncé record : classification bidirectionnelle des termes
`p` (palindromes tels que `6p+1` palindrome). -/
abbrev SpecA083835 : Prop :=
  ∀ {p m m' : ℕ}, IsPal p m → 1 ≤ m →
    (IsPal (6 * p + 1) m' ↔
      (m' = m + 1 ∧ ∀ j < m, dgt p j = 9) ∨
        (m' = m ∧ m % 2 = 1 ∧
          (∀ j, j < m → j % 2 = 0 → dgt p j ≤ 1) ∧
          (∀ j, j < m → j % 2 = 1 → 2 ≤ dgt p j ∧ dgt p j ≤ 3)))
