# Audit d'anteriorite 8 registres - A083833

> SUPERSEDE (2026-11-14) : audit fige a l'etat des registres
> du 08-11. Depuis : record Zenodo publie (concept DOI
> 10.5281/zenodo.24078012, tete 24161963) portant les
> theoremes A083833_C1/C2 ; la fiche OEIS affiche toujours
> « (Conjectures) » en l'absence de soumission du lien.

Date : 2026-11-08. Mission E8-BATCH-3 (sous-agent interne).
Enonce audite (verbatim OEIS, fetch live `search?q=id:A083833&fmt=text`
2026-11-08 ; miroir local de donnees OEIS absent sur cette
machine) :

```
%I A083833 #19 Dec 17 2024
%N A083833 Palindromes p such that 5p + 1 is also a palindrome.
%C A083833 From _Michael S. Branicky_, Jun 13 2021: (Start)
%C A083833 (Conjectures)
%C A083833 All terms contain only the digits {0, 1, 2, 3}.
%C A083833 For d even, the only term with d digits is 2^d;
   equivalently, all terms starting with 1 have odd length. (End)
%K A083833 base,nonn   %O A083833 1,2
%A A083833 _Amarnath Murthy_ and Meenakshi Srikanth, May 09 2003
```

Enonces prouves localement (`lean/A083833.lean`, metadata.json) -
les DEUX conjectures « (Conjectures) » de Branicky (Jun 2021), sous
forme forte, pour toute longueur : `A083833_C1` (tout chiffre de p
est `<= 3`, c.-a-d. alphabet `{0,1,2,3}` - C1 verbatim) et
`A083833_C2` (m pair => tout chiffre de p vaut 2, c.-a-d. p = 22..2 -
C2 verbatim, forme forte). Methode : chaine de retenues
`c_j = (5·(p mod 10^j)+1)/10^j` (`c_0 = 1`, `c_j <= 4`) ; cas m'=m
(chaine symetrique 2-periodique forcant m impair, a_0 = 1, classes
alternees {0,1}/{2,3}) vs cas m'=m+1 (chaine constante forcant
p = 22..2, q = 11..1). Le module prouve aussi les conjectures image
`A083834_C1` / `A083834_C2` (package A083834). Proprietes
universelles ; NON une enumeration : appartenance, completude,
existence, finitude non revendiquees.

## Verdicts par registre

| # | Registre | Methode | Fraicheur | Verdict |
|---|---|---|---|---|
| 1 | Fiche OEIS A083833 | fetch live `?fmt=text` (rev. #19, 17/12/2024) | live 08/11/2026 | les deux conjectures de Branicky restent affichees « (Conjectures) » - aucune preuve referencee ; b-file Branicky n=1..8217 (tous termes a <= 26 chiffres, calcul) ; Mathematica + Python = generation |
| 2 | google-deepmind/formal-conjectures | grep 83833 | HEAD 2055e5a | ABSENT |
| 3 | epoch-research/LeanOpenProblems-results | `git ls-tree` | HEAD cbb7cb65 | ABSENT |
| 4 | provables/sequencelib | find + grep | HEAD dfb06c18 | ABSENT |
| 5 | Repos « OEIS resolues » | oeis-papers (63), OEIS-Settled (5920), Eppie/dvgyl/VictorLiwentao/dpreil, jonmaiga | live 08/11/2026 | ABSENT ; jonmaiga : stub `Prog/A083/A0838.lean`, `Proof/A083/` sans A083833 |
| 6 | Recherche globale `"A083833"` | GitHub code-search (898 hits), arXiv API, web | 08/11/2026 | joeis `A083833.java` + `A083834.java` (calcul), Radcliffe/OEIS-Python (genere), OEIS-Spider, number.house (miroir), notre lean-runner ; reste = collisions ; arXiv : 0 ; forums : 0 |
| 7 | Litterature | « palindrome 5n+1 », carry chain | web 08/11/2026 | aucune preuve publiee des conjectures de Branicky localisee ; famille Murthy/Srikanth 2003 = observations sans preuves referencees |
| 8 | trureturing `dev` | ls-tree + grep | local 2dab9b09 | ABSENT |

## Conclusion

**OUVERT avant ce travail** : aucune preuve anterieure - formelle ou
informelle - des deux conjectures de Branicky (2021) localisee dans
les 8 registres ; la fiche les affiche toujours « (Conjectures) ».
Claim honnete maximal : « preuves verifiees machine des deux
conjectures C1 (alphabet {0,1,2,3}) et C2 (longueur paire =>
repdigit 22..2) pour toute longueur de chiffres, sous leurs formes
fortes » - jamais « premiere preuve » comme revendication de
priorite. Aucune divergence de claim dans le package (metadata :
« theorem-unconditional (C1/C2 prouvees) », enumeration non
revendiquee).
