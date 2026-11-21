# Audit d'anteriorite 8 registres - A083832

Date : 2026-11-08. Mission E8-BATCH-3 (sous-agent le projet).
Enonce audite (verbatim OEIS, fetch live `search?q=id:A083832&fmt=text`
2026-11-08 ; miroir `(workdir interne)` absent sur cette machine) :

```
%I A083832 #10 Apr 06 2017
%N A083832 Palindromes of the form 4n + 1 where n is also a
   palindrome. Palindromes arising in A083831.
%K A083832 base,nonn   %O A083832 1,1
%A A083832 _Amarnath Murthy_ and Meenakshi Srikanth, May 09 2003
```

Enonce prouve localement (`lean/A083832.lean` re-export du theoreme
`A083832_digits` du module `A083831.lean`, metadata.json) :
`A083832_alphabet` : pour tout palindrome p a `m >= 1` chiffres tel
que `q = 4p+1` est aussi palindrome (m' chiffres), chaque chiffre de
q est dans `{1,2,3,5,6,9}` - aucun membre ne contient 0, 4, 7 ou 8.
Propriete universelle des membres, prouvee pour toute longueur par la
chaine de retenues du module compagnon (cas m'=m : symetrique
2-periodique ; cas m'=m+1 : constante 3 forcant p = 88..8). NON une
enumeration : appartenance, completude, optimalite de l'alphabet non
revendiquees.

Note de fiche : l'enonce (alphabet des images q) ne figure PAS dans
les commentaires de la fiche A083832 (aucune conjecture marquee) -
theoreme deduit du projet.

## Verdicts par registre

| # | Registre | Methode | Fraicheur | Verdict |
|---|---|---|---|---|
| 1 | Fiche OEIS A083832 | fetch live `?fmt=text` (rev. #10, 06/04/2017) | live 08/11/2026 | aucune conjecture ni reference ; Mathematica Dale = calcul ; table publiee 33 termes |
| 2 | google-deepmind/formal-conjectures | grep 83832 | HEAD 2055e5a | ABSENT |
| 3 | epoch-research/LeanOpenProblems-results | `git ls-tree` | HEAD cbb7cb65 | ABSENT |
| 4 | provables/sequencelib | find + grep | HEAD dfb06c18 | ABSENT |
| 5 | Repos « OEIS resolues » | oeis-papers (63), OEIS-Settled (5920), Eppie/dvgyl/VictorLiwentao/dpreil, jonmaiga | live 08/11/2026 | ABSENT ; jonmaiga : stub `Prog/A083/A0838.lean`, `Proof/A083/` sans A083832 |
| 6 | Recherche globale `"A083832"` | GitHub code-search (499 hits), arXiv API, web | 08/11/2026 | joeis `A083832.java` (calcul), OEIS-Spider (soeurs), notre hote de build externe ; reste = collisions (logs, fan-subs, hashes) ; arXiv : 0 ; forums : 0 |
| 7 | Litterature | famille Murthy/Srikanth, alphabet des images 4p+1 | web 08/11/2026 | aucune preuve publiee localisee ; enonce absent meme des commentaires OEIS - theoreme deduit |
| 8 | trureturing `dev` | ls-tree + grep | local 2dab9b09 | ABSENT |

## Conclusion

**OUVERT avant ce travail** : aucune preuve anterieure de
l'alphabet `{1,2,3,5,6,9}` pour les palindromes `q = 4p+1` n'a ete
localisee. Claim honnete maximal : « preuve verifiee machine de la
propriete universelle d'alphabet des membres pour toute longueur » -
jamais « premiere preuve » comme revendication de priorite. Aucune
divergence de claim dans le package (metadata : « universal digit-
alphabet property ... enumeration of the sequence not claimed »).
