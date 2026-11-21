# Audit d'anteriorite 8 registres - A083829

Date : 2026-11-08. Audit d'anteriorite interne, lot E8.
Enonce audite (verbatim OEIS, fetch live `search?q=id:A083829&fmt=text`
le 2026-11-08) :

```
%I A083829 #21 Oct 27 2026
%N A083829 Palindromes k such that 3k + 1 is also a palindrome.
%C A083829 From _Robert Israel_, Feb 23 2023: (Start)
%C A083829 Includes A002281. It appears that the only terms with an
   even number of digits are in A002281. All other terms of more than
   1 digit start with 14, 15, 16, 24, 25 or 26. It also appears that
   no terms contain the digits 3, 8 or 9, and the only ones that
   contain 7 are A002281. (End)
%K A083829 base,nonn,changed
%A A083829 _Amarnath Murthy_ and Meenakshi Srikanth, May 09 2003
```

Enonces prouves localement (`lean/A083829.lean`, metadata.json) -
les QUATRE assertions « It appears » d'Israel, pour toute longueur :
`A083829_even` (P1 : membre de longueur paire => repdigit 77..7),
`A083829_digits` (P3 : aucun chiffre 3, 8, 9 - alphabet
`{0,1,2,4,5,6,7}`), `A083829_seven` (P4 : un membre contenant 7 est
tout en 7), `A083829_prefix` (P2 : membre >= 2 chiffres non repdigit
commence par 14/15/16/24/25/26). Methode : chaine de retenues
`c_j = (3·(p mod 10^j)+1)/10^j` (`c_0 = 1`, `c_j <= 2`), cas m'=m
(chaine symetrique 2-periodique, m impair) vs m'=m+1 (etat unique
forcant p = 77..7). Proprietes universelles des membres ; NON une
enumeration : appartenance de valeurs, completude de la liste
publiee, finitude non revendiquees. Le module prouve aussi
`A083830_digits` (soeur, package A083830).

## Verdicts par registre

| # | Registre | Methode | Fraicheur | Verdict |
|---|---|---|---|---|
| 1 | Fiche OEIS A083829 | fetch live `?fmt=text` (rev. #21, 27/10/2026) | live 08/11/2026 | les 4 assertions restent affichees « It appears » - aucune preuve referencee ; b-file Israel n=1..6576 (calcul) ; Maple Israel + Mathematica Dale = generation des termes |
| 2 | google-deepmind/formal-conjectures | grep 83829 | HEAD 2055e5a | ABSENT |
| 3 | epoch-research/LeanOpenProblems-results | `git ls-tree` | HEAD cbb7cb65 | ABSENT |
| 4 | provables/sequencelib | find + grep | HEAD dfb06c18 | ABSENT |
| 5 | Repos « OEIS resolues » | oeis-papers (63), OEIS-Settled (5920), Eppie/dvgyl/VictorLiwentao/dpreil, jonmaiga | live 08/11/2026 | ABSENT ; jonmaiga : stub `Prog/A083/A0838.lean`, `Proof/A083/` ne contient pas A083829 |
| 6 | Recherche globale `"A083829"` | GitHub code-search (465 hits), arXiv API, web | 08/11/2026 | joeis `A083829.java` + `A083830.java` (calcul), OEIS-Spider (donnees soeurs), loda-lang `deny.txt` (« A083455: Duplicate of A083829 » - exclusion de minage, pas une preuve), notre propre depot de CI (resultat auto-reflexif, exclu) ; reste = collisions ; arXiv : 0 ; forums : 0 |
| 7 | Litterature | « palindrome 3n+1 », carry chain | web 08/11/2026 | aucune preuve publiee des assertions d'Israel localisee ; famille Murthy/Srikanth 2003 (A083829-836) = commentaires observatoires sans preuves referencees |
| 8 | trureturing `dev` | ls-tree + grep | local 2dab9b09 | ABSENT |

## Conclusion

**OUVERT avant ce travail** : aucune preuve anterieure - formelle ou
informelle - des quatre assertions « It appears » d'Israel (2023)
localisee dans les 8 registres ; la fiche les affiche toujours comme
observations. Claim honnete maximal : « preuves verifiees machine
(Lean 4, axiomes standard, zero native_decide) des quatre assertions
P1-P4 pour toute longueur de chiffres » - la formulation « aucune
preuve anterieure localisee » decrit l'audit, jamais « premiere
preuve » comme revendication de priorite dans le texte. Aucune
divergence de claim dans le package (metadata : « theorem-unconditional
(P1-P4 prouvees) », enumeration non revendiquee).
