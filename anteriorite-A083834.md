# Audit d'anteriorite 8 registres - A083834

Date : 2026-11-08. Audit d'anteriorite interne, lot E8.
Enonce audite (verbatim OEIS, fetch live `search?q=id:A083834&fmt=text`
le 2026-11-08) :

```
%I A083834 #21 Jun 14 2021
%N A083834 Palindromes of the form 5p + 1 where p is also a
   palindrome. Palindromes arising in A083833.
%C A083834 From _Michael S. Branicky_, Jun 13 2021: (Start)
%C A083834 (Conjectures)
%C A083834 All terms contain only the digits {0, 1, 5, 6}.
%C A083834 For d odd, the only term with d digits is 1^d;
   equivalently, all terms starting with 6 have odd length. (End)
%K A083834 base,nonn   %O A083834 1,1
%A A083834 _Amarnath Murthy_ and Meenakshi Srikanth, May 09 2003
```

Enonces prouves localement (`lean/A083834.lean` re-export de
`A083834_C1` / `A083834_C2` du module `A083833.lean`, metadata.json) :
`A083834_alphabet` (= C1) : tout chiffre de `q = 5p+1` est dans
`{0,1,5,6}` - C1 verbatim de Branicky ; `A083834_repunit` (= C2) : si
la longueur m' de q est PAIRE alors tout chiffre de q vaut 1 (q =
repunit 11..1) - direction unicite de la conjecture C2. Note de
lecture (deja divulguee dans metadata.json) : le verbatim de la
fiche dit « For d odd, the only term with d digits is 1^d » -
incoherent avec les donnees (606, 656 ont 3 chiffres) - tandis que la
clause « equivalently, all terms starting with 6 have odd length »
est non ambigue et correspond au theoreme prouve (longueur paire =>
repunit). Methode : chaine de retenues du module compagnon
(multiplicateur 5). Proprietes universelles ; NON une enumeration :
appartenance, completude, existence, finitude non revendiquees.

## Verdicts par registre

| # | Registre | Methode | Fraicheur | Verdict |
|---|---|---|---|---|
| 1 | Fiche OEIS A083834 | fetch live `?fmt=text` (rev. #21, 14/06/2021) | live 08/11/2026 | les deux conjectures de Branicky restent affichees « (Conjectures) » - aucune preuve referencee ; b-file Branicky n=1..8217 ; Mathematica + Python + PARI Froehlich = generation/test |
| 2 | google-deepmind/formal-conjectures | grep 83834 | HEAD 2055e5a | ABSENT |
| 3 | epoch-research/LeanOpenProblems-results | `git ls-tree` | HEAD cbb7cb65 | ABSENT |
| 4 | provables/sequencelib | find + grep | HEAD dfb06c18 | ABSENT |
| 5 | Repos « OEIS resolues » | oeis-papers (63), OEIS-Settled (5920), Eppie/dvgyl/VictorLiwentao/dpreil, jonmaiga | live 08/11/2026 | ABSENT ; jonmaiga : stub `Prog/A083/A0838.lean`, `Proof/A083/` sans A083834 |
| 6 | Recherche globale `"A083834"` | GitHub code-search (527 hits), arXiv API, web | 08/11/2026 | joeis `A083834.java` (calcul), Radcliffe/OEIS-Python (genere), OEIS-Spider, number.house (miroir), notre propre depot de CI (resultat auto-reflexif, exclu) ; reste = collisions (notebooks recruit-visitor, Kdb pcb) ; arXiv : 0 ; forums : 0 |
| 7 | Litterature | « palindrome 5n+1 repunit » | web 08/11/2026 | aucune preuve publiee des conjectures de Branicky localisee ; la lecture corrigee (pair vs impair) est documentee dans le package |
| 8 | trureturing `dev` | ls-tree + grep | local 2dab9b09 | ABSENT |

## Conclusion

**OUVERT avant ce travail** : aucune preuve anterieure des deux
conjectures de Branicky sur les images `q = 5p+1` localisee ; la
fiche les affiche toujours « (Conjectures) ». Claim honnete maximal :
« preuves verifiees machine de C1 (alphabet {0,1,5,6}) et de la
direction unicite de C2 (longueur paire => repunit) pour toute
longueur » - jamais « premiere preuve » comme revendication de
priorite ; la clause « d odd » du verbatim reste un enonce
incoherent avec les donnees, non reproduit comme claim (le package
le documente correctement). Aucune divergence de claim dans le
package (metadata : « uniqueness direction ... enumeration of the
sequence not claimed »).
